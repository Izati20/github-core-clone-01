// main.ts — a GitHub-compatible git forge in one file, Node standard library only.
//
// Serves the GitHub REST v3 surface the conformance suite exercises, plus the git smart-HTTP
// protocol (v0 and v2) with packfile read/write. All state is in memory; ids, ordering and
// timestamps derive from sequential counters and a logical clock, so the same request sequence
// always produces the same responses.

import { createServer, request as httpRequest, type IncomingMessage, type ServerResponse } from 'node:http';
import { request as httpsRequest } from 'node:https';
import { createHash, timingSafeEqual } from 'node:crypto';
import { deflateSync, inflateSync, constants as zlibConstants } from 'node:zlib';

// --------------------------------------------------------------------------- constants

const ZERO_OID = '0000000000000000000000000000000000000000';
const TYPE_IDS: Record<string, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const TYPE_NAMES: Record<number, string> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag', 6: 'ofs-delta', 7: 'ref-delta' };
const FORGE_VERSION = '1.0.0';
const COMMITTER = { name: 'makefun forge', email: 'forge@example.invalid' };
/** Logical clock base: 2026-01-01T00:00:00Z. Every timestamp the forge emits is base + tick. */
const CLOCK_BASE_SEC = 1_767_225_600;

let clockTick = 0;
function nowSec(): number {
  clockTick += 1;
  return CLOCK_BASE_SEC + clockTick;
}
function isoOf(sec: number): string {
  return new Date(sec * 1000).toISOString();
}
function stampNow(): { sec: number; iso: string } {
  const sec = nowSec();
  return { sec, iso: isoOf(sec) };
}

// --------------------------------------------------------------------------- git object engine

interface GitObject {
  type: string; // commit | tree | blob | tag
  data: Buffer;
}

function hashObject(type: string, data: Buffer): string {
  const hash = createHash('sha1');
  hash.update(`${type} ${data.length}\0`, 'utf8');
  hash.update(data);
  return hash.digest('hex');
}

function sha1Hex(data: Buffer): string {
  return createHash('sha1').update(data).digest('hex');
}

function isOid(value: string): boolean {
  return /^[0-9a-f]{40}$/i.test(value);
}

// ---- tree codec

interface TreeEntry {
  mode: string; // e.g. '100644', '100755', '120000', '40000' (dir, as stored), '160000'
  name: string;
  oid: string;
}

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let pos = 0;
  while (pos < data.length) {
    const space = data.indexOf(0x20, pos);
    const nul = data.indexOf(0x00, space);
    const mode = data.toString('utf8', pos, space);
    const name = data.toString('utf8', space + 1, nul);
    const oid = data.toString('hex', nul + 1, nul + 21);
    entries.push({ mode, name, oid });
    pos = nul + 21;
  }
  return entries;
}

/** Git's tree sort: by name, with directories compared as if their name ended in '/'. */
function treeSortKey(entry: TreeEntry): string {
  return entry.mode === '40000' ? `${entry.name}/` : entry.name;
}

function buildTree(entries: TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => {
    const ka = treeSortKey(a);
    const kb = treeSortKey(b);
    return ka < kb ? -1 : ka > kb ? 1 : 0;
  });
  const parts: Buffer[] = [];
  for (const entry of sorted) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

// ---- commit codec

interface CommitInfo {
  tree: string;
  parents: string[];
  message: string;
  authorLine: string;
  committerLine: string;
  timestamp: number;
}

/**
 * Commit parsing is memoized on the data buffer itself: stored object buffers are immutable
 * and never reused for different content, so a buffer identity is an exact cache key. Ancestor
 * walks and fetch planning re-parse the same commits constantly without this.
 */
const commitInfoCache = new WeakMap<Buffer, CommitInfo>();

function parseCommit(data: Buffer): CommitInfo {
  const cached = commitInfoCache.get(data);
  if (cached !== undefined) return cached;
  const info = parseCommitRaw(data);
  commitInfoCache.set(data, info);
  return info;
}

function parseCommitRaw(data: Buffer): CommitInfo {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const header = split === -1 ? text : text.slice(0, split);
  const message = split === -1 ? '' : text.slice(split + 2);
  let tree = '';
  const parents: string[] = [];
  let authorLine = '';
  let committerLine = '';
  let timestamp = 0;
  for (const line of header.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) {
      authorLine = line.slice(7);
      const match = / (\d+) [+-]\d{4}$/.exec(authorLine);
      if (match) timestamp = Number(match[1]);
    } else if (line.startsWith('committer ')) committerLine = line.slice(10);
  }
  return { tree, parents, message, authorLine, committerLine, timestamp };
}

function buildCommit(input: {
  tree: string;
  parents: string[];
  message: string;
  authorName: string;
  authorEmail: string;
  timestamp: number;
}): Buffer {
  const ident = `${input.authorName} <${input.authorEmail}> ${input.timestamp} +0000`;
  const lines = [`tree ${input.tree}`];
  for (const parent of input.parents) lines.push(`parent ${parent}`);
  lines.push(`author ${ident}`);
  lines.push(`committer ${ident}`);
  return Buffer.from(`${lines.join('\n')}\n\n${input.message}`, 'utf8');
}

/** Split an ident line ("Name <email> ts tz") into the REST author shape. */
function identJson(line: string, fallbackSec: number): { name: string; email: string; date: string } {
  const match = /^(.*?) <(.*?)> (\d+) [+-]\d{4}$/.exec(line);
  if (!match) return { name: line, email: '', date: isoOf(fallbackSec) };
  return { name: match[1] ?? '', email: match[2] ?? '', date: isoOf(Number(match[3])) };
}

// ---- tag codec

function parseTagTarget(data: Buffer): string | null {
  const text = data.toString('utf8');
  const match = /^object ([0-9a-f]{40})$/m.exec(text);
  return match ? (match[1] as string) : null;
}

// ---- packfiles

/**
 * Inflate one deflate stream starting at `offset` and report how many bytes it consumed.
 *
 * Fast path: `inflateSync` with `{ info: true }` returns the zlib engine alongside the data,
 * and the engine's `bytesWritten` is exactly how many input bytes the stream consumed (it
 * stops at the stream's end and ignores trailing bytes). That turns the ~log2(n) throwaway
 * inflations of the search below into a single pass — pack parsing was the forge's top CPU
 * cost (one binary search per object, most attempts throwing). The result is only trusted
 * when the inflated length matches the header's size, and parsePack additionally requires a
 * fast parse to land exactly on the pack trailer; any doubt re-runs the whole pack through
 * the search path, so a runtime whose engine does not report consumption behaves exactly
 * like the original implementation.
 */
function inflateAt(buffer: Buffer, offset: number, expectedSize: number, fast: boolean): { data: Buffer; consumed: number } {
  if (fast) {
    try {
      const result = inflateSync(buffer.subarray(offset), { info: true }) as unknown as {
        buffer?: Buffer;
        engine?: { bytesWritten?: unknown };
      };
      const data = result?.buffer;
      const consumed = result?.engine?.bytesWritten;
      if (
        Buffer.isBuffer(data) &&
        data.length === expectedSize &&
        typeof consumed === 'number' &&
        consumed >= 2 &&
        consumed <= buffer.length - offset
      ) {
        return { data, consumed };
      }
    } catch {
      // Not a well-formed stream here; the search reports the failure the original way.
    }
  }
  return inflateAtSearch(buffer, offset, expectedSize);
}

/**
 * The original exact search: inflateSync ignores trailing bytes and throws on a truncated
 * stream, so the stream's end is the smallest prefix that inflates successfully — a binary
 * search over the prefix length finds it exactly.
 */
function inflateAtSearch(buffer: Buffer, offset: number, expectedSize: number): { data: Buffer; consumed: number } {
  let lo = offset; // known to fail (too short)
  let hi = buffer.length; // the whole rest always succeeds for a well-formed stream
  const attempt = (end: number): Buffer | null => {
    try {
      const out = inflateSync(buffer.subarray(offset, end));
      return out.length === expectedSize ? out : null;
    } catch {
      return null;
    }
  };
  const whole = attempt(hi);
  if (whole === null) throw new Error('pack object does not inflate');
  while (hi - lo > 1) {
    const mid = lo + Math.floor((hi - lo) / 2);
    if (attempt(mid) !== null) hi = mid;
    else lo = mid;
  }
  const data = attempt(hi);
  if (data === null) throw new Error('pack object does not inflate');
  return { data, consumed: hi - offset };
}

function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let pos = 0;
  const readVarint = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[pos] as number;
      pos += 1;
      value += (byte & 0x7f) * 2 ** shift;
      shift += 7;
      if ((byte & 0x80) === 0) break;
    }
    return value;
  };
  const sourceSize = readVarint();
  const targetSize = readVarint();
  if (sourceSize !== base.length) throw new Error(`delta base size mismatch: ${sourceSize} != ${base.length}`);
  const parts: Buffer[] = [];
  let produced = 0;
  while (pos < delta.length) {
    const opcode = delta[pos] as number;
    pos += 1;
    if (opcode & 0x80) {
      let offset = 0;
      let size = 0;
      for (let bit = 0; bit < 4; bit += 1) {
        if (opcode & (1 << bit)) {
          offset += (delta[pos] as number) * 2 ** (8 * bit);
          pos += 1;
        }
      }
      for (let bit = 0; bit < 3; bit += 1) {
        if (opcode & (0x10 << bit)) {
          size += (delta[pos] as number) * 2 ** (8 * bit);
          pos += 1;
        }
      }
      if (size === 0) size = 0x10000;
      parts.push(base.subarray(offset, offset + size));
      produced += size;
    } else if (opcode > 0) {
      parts.push(delta.subarray(pos, pos + opcode));
      produced += opcode;
      pos += opcode;
    } else {
      throw new Error('delta opcode 0 is reserved');
    }
  }
  const out = Buffer.concat(parts);
  if (out.length !== targetSize || produced !== targetSize) throw new Error('delta result size mismatch');
  return out;
}

interface PackEntry {
  oid: string;
  type: string;
  data: Buffer;
}

/**
 * Parse a whole packfile into resolved objects. `lookup` resolves REF_DELTA bases that live
 * outside the pack (thin packs); OFS_DELTA bases are always in-pack.
 */
/**
 * Parse a pack, fastest first: a fast parse is accepted only when it consumes the pack
 * exactly up to the trailer; anything else (a throw, a short or overlong end) re-runs the
 * whole pack through the search-based parse, which is the original behavior verbatim.
 */
function parsePack(pack: Buffer, lookup: (oid: string) => GitObject | undefined): PackEntry[] {
  try {
    const fast = parsePackImpl(pack, lookup, true);
    if (fast.endPos === pack.length - 20) return fast.entries;
  } catch {
    // Fall through to the search parse, which raises the definitive error.
  }
  return parsePackImpl(pack, lookup, false).entries;
}

function parsePackImpl(pack: Buffer, lookup: (oid: string) => GitObject | undefined, fast: boolean): { entries: PackEntry[]; endPos: number } {
  if (pack.length < 32 || pack.toString('latin1', 0, 4) !== 'PACK') throw new Error('not a packfile');
  const version = pack.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`unsupported pack version ${version}`);
  const count = pack.readUInt32BE(8);
  const trailer = pack.subarray(pack.length - 20);
  const digest = createHash('sha1').update(pack.subarray(0, pack.length - 20)).digest();
  if (!timingSafeEqual(digest, trailer)) throw new Error('pack checksum mismatch');

  interface RawEntry {
    offset: number;
    type: string;
    data?: Buffer;
    baseOid?: string;
    baseOffset?: number;
  }
  const raw: RawEntry[] = [];
  const byOffset = new Map<number, RawEntry>();
  let pos = 12;
  for (let index = 0; index < count; index += 1) {
    const offset = pos;
    let byte = pack[pos] as number;
    pos += 1;
    const typeId = (byte >> 4) & 7;
    let size = byte & 0x0f;
    let shift = 4;
    while (byte & 0x80) {
      byte = pack[pos] as number;
      pos += 1;
      size += (byte & 0x7f) * 2 ** shift;
      shift += 7;
    }
    const type = TYPE_NAMES[typeId] ?? '';
    const entry: RawEntry = { offset, type };
    if (type === 'ofs-delta') {
      let b = pack[pos] as number;
      pos += 1;
      let back = b & 0x7f;
      while (b & 0x80) {
        b = pack[pos] as number;
        pos += 1;
        back = ((back + 1) << 7) | (b & 0x7f);
      }
      entry.baseOffset = offset - back;
    } else if (type === 'ref-delta') {
      entry.baseOid = pack.toString('hex', pos, pos + 20);
      pos += 20;
    }
    const inflated = inflateAt(pack, pos, size, fast);
    pos += inflated.consumed;
    if (type === 'ofs-delta' || type === 'ref-delta') entry.data = inflated.data; // delta instructions
    else entry.data = inflated.data;
    entry.type = type;
    raw.push(entry);
    byOffset.set(offset, entry);
  }

  const resolved = new Map<number, GitObject>();
  const resolveEntry = (entry: RawEntry): GitObject => {
    const cached = resolved.get(entry.offset);
    if (cached) return cached;
    let object: GitObject;
    if (entry.type === 'ofs-delta') {
      const baseEntry = byOffset.get(entry.baseOffset as number);
      if (!baseEntry) throw new Error('ofs-delta base missing from pack');
      const base = resolveEntry(baseEntry);
      object = { type: base.type, data: applyDelta(base.data, entry.data as Buffer) };
    } else if (entry.type === 'ref-delta') {
      let base = resolvedByOid(entry.baseOid as string);
      if (!base) base = lookup(entry.baseOid as string);
      if (!base) throw new Error(`ref-delta base ${entry.baseOid} not found`);
      object = { type: base.type, data: applyDelta(base.data, entry.data as Buffer) };
    } else {
      object = { type: entry.type, data: entry.data as Buffer };
    }
    resolved.set(entry.offset, object);
    return object;
  };
  const resolvedByOid = (oid: string): GitObject | undefined => {
    for (const entry of raw) {
      if (entry.type === 'ofs-delta' || entry.type === 'ref-delta') continue;
      if (hashObject(entry.type, entry.data as Buffer) === oid) return { type: entry.type, data: entry.data as Buffer };
    }
    return undefined;
  };

  const entries: PackEntry[] = [];
  for (const entry of raw) {
    const object = resolveEntry(entry);
    entries.push({ oid: hashObject(object.type, object.data), type: object.type, data: object.data });
  }
  return { entries, endPos: pos };
}

/** Write a packfile carrying exactly `objects`, in the given order, with no deltas. */
function writePack(objects: readonly GitObject[]): Buffer {
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'latin1');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(objects.length, 8);
  const parts: Buffer[] = [header];
  for (const object of objects) {
    const typeId = TYPE_IDS[object.type] as number;
    let size = object.data.length;
    const first = (typeId << 4) | (size & 0x0f);
    size = Math.floor(size / 16);
    const bytes: number[] = [];
    if (size > 0) {
      bytes.push(first | 0x80);
      while (size > 0) {
        const next = size & 0x7f;
        size = Math.floor(size / 128);
        bytes.push(size > 0 ? next | 0x80 : next);
      }
    } else {
      bytes.push(first);
    }
    parts.push(Buffer.from(bytes));
    parts.push(deflateSync(object.data, { level: zlibConstants.Z_BEST_SPEED }));
  }
  const body = Buffer.concat(parts);
  const trailer = createHash('sha1').update(body).digest();
  return Buffer.concat([body, trailer]);
}

// --------------------------------------------------------------------------- store

interface LabelRec {
  id: number;
  name: string;
  color: string;
  description: string | null;
}

interface IssueRec {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[]; // label names
  createdSec: number;
  updatedSec: number;
}

interface CommentRec {
  id: number;
  issueNumber: number;
  body: string;
  createdSec: number;
  updatedSec: number;
}

interface PullRec {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  headRef: string; // branch name
  baseRef: string; // branch name
  headShaAtCreate: string;
  merged: boolean;
  mergedAtSec: number | null;
  mergeCommitSha: string | null;
  createdSec: number;
  updatedSec: number;
}

interface Repo {
  id: number;
  owner: string | null; // learned from the first owner-bearing path that names this repo
  name: string;
  description: string | null;
  isPrivate: boolean;
  defaultBranch: string;
  objects: Map<string, GitObject>;
  refs: Map<string, string>; // full ref name -> oid
  labels: Map<string, LabelRec>;
  issues: Map<number, IssueRec>;
  comments: Map<number, CommentRec[]>; // issue number -> comments in creation order
  pulls: Map<number, PullRec>;
  nextNumber: number; // shared issue/PR number sequence, as on GitHub
  createdSec: number;
  updatedSec: number;
}

const reposByName = new Map<string, Repo>();
let nextRepoId = 1;
let nextLabelId = 1;
let nextIssueId = 1;
let nextCommentId = 1;
let nextPullId = 1;
/** The login the bearer token names; learned from the first owner-bearing request path. */
let viewerLogin: string | null = null;

function learnViewer(owner: string): void {
  if (viewerLogin === null && owner !== '') viewerLogin = owner;
}

/**
 * Resolve a repo for an owner-bearing path. The token's repositories live under the viewer's
 * login; the same name under any other login does not exist (404, never 403).
 */
function repoForPath(owner: string, name: string): Repo | null {
  const repo = reposByName.get(name);
  if (!repo) return null;
  if (repo.owner === null) {
    repo.owner = owner;
    learnViewer(owner);
    return repo;
  }
  if (repo.owner !== owner) return null;
  return repo;
}

function createRepoRecord(name: string, description: string | null, isPrivate: boolean): Repo {
  const stamp = stampNow();
  const repo: Repo = {
    id: nextRepoId,
    owner: viewerLogin,
    name,
    description,
    isPrivate,
    defaultBranch: 'main',
    objects: new Map(),
    refs: new Map(),
    labels: new Map(),
    issues: new Map(),
    comments: new Map(),
    pulls: new Map(),
    nextNumber: 1,
    createdSec: stamp.sec,
    updatedSec: stamp.sec,
  };
  nextRepoId += 1;
  reposByName.set(name, repo);
  return repo;
}

function headRefOf(repo: Repo): string {
  return `refs/heads/${repo.defaultBranch}`;
}

function storeObject(repo: Repo, type: string, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}

// ---- tree path operations (the contents API's view of a commit)

/** Flatten a tree (recursively) into path -> blob entry. Directories map to their tree oid too. */
function flattenTree(repo: Repo, treeOid: string, prefix: string, out: Map<string, { oid: string; mode: string; isDir: boolean }>): void {
  const tree = repo.objects.get(treeOid);
  if (!tree || tree.type !== 'tree') return;
  for (const entry of parseTree(tree.data)) {
    const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
    const isDir = entry.mode === '40000';
    out.set(path, { oid: entry.oid, mode: entry.mode, isDir });
    if (isDir) flattenTree(repo, entry.oid, path, out);
  }
}

function treeMapOfCommit(repo: Repo, commitOid: string): Map<string, { oid: string; mode: string; isDir: boolean }> {
  const out = new Map<string, { oid: string; mode: string; isDir: boolean }>();
  const commit = repo.objects.get(commitOid);
  if (!commit || commit.type !== 'commit') return out;
  flattenTree(repo, parseCommit(commit.data).tree, '', out);
  return out;
}

/** Files only: path -> blob oid, for diffs and merges. */
function fileMapOfCommit(repo: Repo, commitOid: string): Map<string, string> {
  const out = new Map<string, string>();
  for (const [path, entry] of treeMapOfCommit(repo, commitOid)) {
    if (!entry.isDir) out.set(path, entry.oid);
  }
  return out;
}

/** Rebuild a root tree from a flat path -> {oid, mode} file map, storing every new tree. */
function buildTreeFromFiles(repo: Repo, files: Map<string, { oid: string; mode: string }>): string {
  interface DirNode {
    files: { name: string; oid: string; mode: string }[];
    dirs: Map<string, DirNode>;
  }
  const root: DirNode = { files: [], dirs: new Map() };
  for (const [path, file] of files) {
    const segments = path.split('/');
    let node = root;
    for (let i = 0; i < segments.length - 1; i += 1) {
      const segment = segments[i] as string;
      let next = node.dirs.get(segment);
      if (!next) {
        next = { files: [], dirs: new Map() };
        node.dirs.set(segment, next);
      }
      node = next;
    }
    node.files.push({ name: segments[segments.length - 1] as string, oid: file.oid, mode: file.mode });
  }
  const emit = (node: DirNode): string => {
    const entries: TreeEntry[] = [];
    for (const file of node.files) entries.push({ mode: file.mode, name: file.name, oid: file.oid });
    for (const [name, dir] of node.dirs) entries.push({ mode: '40000', name, oid: emit(dir) });
    return storeObject(repo, 'tree', buildTree(entries));
  };
  return emit(root);
}

/** Create a commit on top of `parent` (null for a root commit) and return its oid. */
function makeCommit(repo: Repo, input: { tree: string; parent: string | null; message: string }): string {
  const stamp = stampNow();
  const data = buildCommit({
    tree: input.tree,
    parents: input.parent === null ? [] : [input.parent],
    message: input.message,
    authorName: COMMITTER.name,
    authorEmail: COMMITTER.email,
    timestamp: stamp.sec,
  });
  return storeObject(repo, 'commit', data);
}

/** Resolve a REST ref parameter (branch name, full ref, tag name or commit oid) to a commit oid. */
function resolveRefToCommit(repo: Repo, ref: string): string | null {
  if (isOid(ref)) {
    const object = repo.objects.get(ref.toLowerCase());
    if (object) {
      if (object.type === 'commit') return ref.toLowerCase();
      if (object.type === 'tag') {
        const target = parseTagTarget(object.data);
        return target === null ? null : resolveRefToCommit(repo, target);
      }
    }
    return null;
  }
  const candidates = [`refs/heads/${ref}`, `refs/tags/${ref}`, ref];
  for (const candidate of candidates) {
    const oid = repo.refs.get(candidate);
    if (oid !== undefined) {
      const object = repo.objects.get(oid);
      if (object?.type === 'tag') {
        const target = parseTagTarget(object.data);
        if (target !== null) return target;
      }
      return oid;
    }
  }
  return null;
}

/** All ancestors of a commit (including itself), newest first (parents before older ancestors). */
function ancestorsOf(repo: Repo, tip: string): string[] {
  const order: string[] = [];
  const seen = new Set<string>();
  const queue: string[] = [tip];
  while (queue.length > 0) {
    const oid = queue.shift() as string;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const object = repo.objects.get(oid);
    if (!object || object.type !== 'commit') continue;
    order.push(oid);
    for (const parent of parseCommit(object.data).parents) queue.push(parent);
  }
  return order;
}

/**
 * Membership test with early exit: walk parents from the descendant and stop the moment the
 * ancestor turns up. A fast-forward check (the receive-pack hot path) almost always finds its
 * answer one or two steps back; building the descendant's whole ancestry first made every
 * push cost O(chain length).
 */
function isAncestor(repo: Repo, ancestor: string, descendant: string): boolean {
  if (ancestor === descendant) return true;
  const seen = new Set<string>();
  const stack: string[] = [descendant];
  while (stack.length > 0) {
    const oid = stack.pop() as string;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const object = repo.objects.get(oid);
    if (!object || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) {
      if (parent === ancestor) return true;
      stack.push(parent);
    }
  }
  return false;
}

function mergeBase(repo: Repo, a: string, b: string): string | null {
  const ancestorsA = new Set(ancestorsOf(repo, a));
  for (const candidate of ancestorsOf(repo, b)) {
    if (ancestorsA.has(candidate)) return candidate;
  }
  return null;
}

// ---- fetch object selection

interface FetchPlan {
  objects: GitObject[]; // in pack order: commits, then trees, then blobs/tags
  shallow: string[];
  unshallow: string[];
}

/**
 * The object set for one fetch: everything reachable from the wants (depth-limited when
 * `deepen` is set) that the client does not already have. The client's shallow commits cut
 * the have-closure: their parents are not treated as held.
 */
function planFetch(repo: Repo, wants: string[], haves: string[], clientShallow: Set<string>, deepen: number | null): FetchPlan {
  // Have-closure: objects the client can already reach.
  const have = new Set<string>();
  const haveStack: string[] = [...haves];
  while (haveStack.length > 0) {
    const oid = haveStack.pop() as string;
    if (have.has(oid)) continue;
    const object = repo.objects.get(oid);
    if (!object) continue;
    have.add(oid);
    if (object.type === 'commit') {
      const info = parseCommit(object.data);
      haveStack.push(info.tree);
      if (!clientShallow.has(oid)) for (const parent of info.parents) haveStack.push(parent);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) haveStack.push(entry.oid);
    } else if (object.type === 'tag') {
      const target = parseTagTarget(object.data);
      if (target !== null) haveStack.push(target);
    }
  }

  // Want-closure, with commit generations for the depth limit.
  const generation = new Map<string, number>();
  const wantObjects = new Set<string>();
  const commitQueue: { oid: string; gen: number }[] = [];
  const pushObjectClosure = (rootOid: string): void => {
    const stack: string[] = [rootOid];
    while (stack.length > 0) {
      const oid = stack.pop() as string;
      if (wantObjects.has(oid)) continue;
      const object = repo.objects.get(oid);
      if (!object) continue;
      wantObjects.add(oid);
      if (object.type === 'tree') {
        for (const entry of parseTree(object.data)) stack.push(entry.oid);
      } else if (object.type === 'tag') {
        const target = parseTagTarget(object.data);
        if (target !== null) stack.push(target);
      }
    }
  };
  for (const want of wants) {
    const object = repo.objects.get(want);
    if (!object) continue;
    if (object.type === 'commit') {
      if (!generation.has(want)) {
        generation.set(want, 0);
        commitQueue.push({ oid: want, gen: 0 });
      }
    } else {
      pushObjectClosure(want);
    }
  }
  while (commitQueue.length > 0) {
    const { oid, gen } = commitQueue.shift() as { oid: string; gen: number };
    if (deepen !== null && gen >= deepen) continue;
    const object = repo.objects.get(oid);
    if (!object || object.type !== 'commit') continue;
    const info = parseCommit(object.data);
    pushObjectClosure(info.tree);
    wantObjects.add(oid);
    for (const parent of info.parents) {
      const parentGen = gen + 1;
      if (deepen !== null && parentGen >= deepen) continue;
      if (!generation.has(parent) || (generation.get(parent) as number) > parentGen) {
        generation.set(parent, parentGen);
        commitQueue.push({ oid: parent, gen: parentGen });
      }
    }
  }

  const send = new Set<string>();
  for (const oid of wantObjects) {
    if (!have.has(oid)) send.add(oid);
  }

  // Shallow bookkeeping: a sent (or wanted) commit whose parent stays unavailable is shallow;
  // a previously shallow commit whose parents all became available is unshallowed.
  const available = new Set<string>([...have, ...send]);
  const shallow: string[] = [];
  const unshallow: string[] = [];
  if (deepen !== null || clientShallow.size > 0) {
    for (const oid of send) {
      const object = repo.objects.get(oid);
      if (!object || object.type !== 'commit') continue;
      const info = parseCommit(object.data);
      if (info.parents.some((parent) => !available.has(parent))) shallow.push(oid);
    }
    for (const oid of clientShallow) {
      const object = repo.objects.get(oid);
      if (!object || object.type !== 'commit') continue;
      const info = parseCommit(object.data);
      if (info.parents.every((parent) => available.has(parent))) unshallow.push(oid);
    }
  }
  shallow.sort();
  unshallow.sort();

  const commits: GitObject[] = [];
  const trees: GitObject[] = [];
  const rest: GitObject[] = [];
  for (const oid of send) {
    const object = repo.objects.get(oid) as GitObject;
    if (object.type === 'commit') commits.push(object);
    else if (object.type === 'tree') trees.push(object);
    else rest.push(object);
  }
  // Deterministic pack order: commits by generation, then trees, then the rest, each by oid.
  const byOid = (a: GitObject, b: GitObject): number => {
    const x = hashObject(a.type, a.data);
    const y = hashObject(b.type, b.data);
    return x < y ? -1 : x > y ? 1 : 0;
  };
  commits.sort((a, b) => {
    const ga = generation.get(hashObject(a.type, a.data)) ?? 0;
    const gb = generation.get(hashObject(b.type, b.data)) ?? 0;
    return ga !== gb ? ga - gb : byOid(a, b);
  });
  trees.sort(byOid);
  rest.sort(byOid);
  return { objects: [...commits, ...trees, ...rest], shallow, unshallow };
}

// --------------------------------------------------------------------------- pkt-lines

function pktLine(payload: string | Buffer): Buffer {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const length = body.length + 4;
  const header = Buffer.from(length.toString(16).padStart(4, '0'), 'latin1');
  return Buffer.concat([header, body]);
}
const PKT_FLUSH = Buffer.from('0000', 'latin1');
const PKT_DELIM = Buffer.from('0001', 'latin1');

interface PktFrame {
  kind: 'data' | 'flush' | 'delim';
  payload: Buffer;
}

/** Decode as many complete frames as `buffer` holds; returns the frames and the undecoded rest. */
function decodePktFrames(buffer: Buffer): { frames: PktFrame[]; rest: Buffer } {
  const frames: PktFrame[] = [];
  let pos = 0;
  while (pos + 4 <= buffer.length) {
    const header = buffer.toString('latin1', pos, pos + 4);
    if (!/^[0-9a-f]{4}$/i.test(header)) break;
    const length = parseInt(header, 16);
    if (length === 0) {
      frames.push({ kind: 'flush', payload: Buffer.alloc(0) });
      pos += 4;
      continue;
    }
    if (length === 1) {
      frames.push({ kind: 'delim', payload: Buffer.alloc(0) });
      pos += 4;
      continue;
    }
    if (length === 2 || length === 3) {
      frames.push({ kind: 'data', payload: Buffer.alloc(0) });
      pos += 4;
      continue;
    }
    if (pos + length > buffer.length) break;
    frames.push({ kind: 'data', payload: buffer.subarray(pos + 4, pos + length) });
    pos += length;
  }
  return { frames, rest: buffer.subarray(pos) };
}

function frameText(frame: PktFrame): string {
  return frame.payload.toString('utf8').replace(/\n$/, '');
}

/** Split a sideband stream into band-1 payloads (each at most `chunk` bytes) as pkt-lines. */
function sidebandPackets(data: Buffer, chunk = 65_000): Buffer[] {
  const packets: Buffer[] = [];
  for (let offset = 0; offset < data.length; offset += chunk) {
    const slice = data.subarray(offset, Math.min(data.length, offset + chunk));
    packets.push(pktLine(Buffer.concat([Buffer.from([1]), slice])));
  }
  return packets;
}

// --------------------------------------------------------------------------- git smart HTTP

const UPLOAD_CAPS_V0 = 'multi_ack_detailed side-band-64k ofs-delta shallow';
const RECEIVE_CAPS_V0 = 'report-status side-band-64k delete-refs ofs-delta';

interface RefLine {
  oid: string;
  name: string;
}

function sortedRefs(repo: Repo): RefLine[] {
  return [...repo.refs.entries()]
    .map(([name, oid]) => ({ name, oid }))
    .sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
}

/** The v0 ref advertisement body (after the `# service=` preamble): HEAD first, refs sorted. */
function advertisementV0(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const caps = service === 'git-upload-pack' ? UPLOAD_CAPS_V0 : RECEIVE_CAPS_V0;
  const headTarget = headRefOf(repo);
  const headOid = repo.refs.get(headTarget);
  const refs = sortedRefs(repo);
  const lines: Buffer[] = [];
  const withCaps = (text: string): string => `${text}\0${caps} symref=HEAD:${headTarget} agent=forge/${FORGE_VERSION}`;
  if (refs.length === 0) {
    lines.push(pktLine(withCaps(`${ZERO_OID} capabilities^{}`)));
  } else {
    let first = true;
    if (headOid !== undefined) {
      lines.push(pktLine(withCaps(`${headOid} HEAD`)));
      first = false;
    }
    for (const ref of refs) {
      const text = `${ref.oid} ${ref.name}`;
      lines.push(pktLine(first ? withCaps(text) : text));
      first = false;
      const object = repo.objects.get(ref.oid);
      if (object?.type === 'tag') {
        const target = parseTagTarget(object.data);
        if (target !== null) lines.push(pktLine(`${target} ${ref.name}^{}`));
      }
    }
  }
  return Buffer.concat([...lines, PKT_FLUSH]);
}

function advertisementV2(): Buffer {
  const lines = [
    pktLine('version 2\n'),
    pktLine(`agent=forge/${FORGE_VERSION}\n`),
    pktLine('ls-refs=unborn\n'),
    pktLine('fetch=shallow wait-for-done\n'),
    pktLine('object-format=sha1\n'),
    PKT_FLUSH,
  ];
  return Buffer.concat(lines);
}

function handleInfoRefs(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack', protocolHeader: string | null): { contentType: string; body: Buffer } {
  const contentType = `application/x-${service}-advertisement`;
  if (service === 'git-upload-pack' && protocolHeader !== null && /(^|[,= ])version=2\b/.test(protocolHeader)) {
    return { contentType, body: advertisementV2() };
  }
  const preamble = Buffer.concat([pktLine(`# service=${service}\n`), PKT_FLUSH]);
  return { contentType, body: Buffer.concat([preamble, advertisementV0(repo, service)]) };
}

interface LsRefsArgs {
  peel: boolean;
  symrefs: boolean;
  unborn: boolean;
  prefixes: string[];
}

function handleLsRefs(repo: Repo, args: LsRefsArgs): Buffer {
  const lines: Buffer[] = [];
  const headTarget = headRefOf(repo);
  const headOid = repo.refs.get(headTarget);
  const matchesPrefix = (name: string): boolean => args.prefixes.length === 0 || args.prefixes.some((prefix) => name.startsWith(prefix));
  if (args.prefixes.length === 0) {
    if (headOid !== undefined) {
      lines.push(pktLine(`${headOid} HEAD${args.symrefs ? ` symref-target:${headTarget}` : ''}\n`));
    } else if (args.unborn) {
      lines.push(pktLine(`unborn HEAD${args.symrefs ? ` symref-target:${headTarget}` : ''}\n`));
    }
  }
  for (const ref of sortedRefs(repo)) {
    if (!matchesPrefix(ref.name)) continue;
    let line = `${ref.oid} ${ref.name}`;
    if (args.peel) {
      const object = repo.objects.get(ref.oid);
      if (object?.type === 'tag') {
        const target = parseTagTarget(object.data);
        if (target !== null) line += ` peeled:${target}`;
      }
    }
    lines.push(pktLine(`${line}\n`));
  }
  lines.push(PKT_FLUSH);
  return Buffer.concat(lines);
}

function fetchResponseV2(repo: Repo, wants: string[], haves: string[], clientShallow: Set<string>, deepen: number | null, done: boolean): Buffer {
  if (!done) {
    return Buffer.concat([pktLine('acknowledgments\n'), pktLine('ready\n'), PKT_FLUSH]);
  }
  const plan = planFetch(repo, wants, haves, clientShallow, deepen);
  const parts: Buffer[] = [];
  if (plan.shallow.length > 0 || plan.unshallow.length > 0) {
    parts.push(pktLine('shallow-info\n'));
    for (const oid of plan.shallow) parts.push(pktLine(`shallow ${oid}\n`));
    for (const oid of plan.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
    parts.push(PKT_FLUSH);
  }
  parts.push(pktLine('packfile\n'));
  const pack = writePack(plan.objects);
  parts.push(...sidebandPackets(pack));
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

function fetchResponseV0(repo: Repo, wants: string[], haves: string[], clientShallow: Set<string>, deepen: number | null): Buffer {
  const plan = planFetch(repo, wants, haves, clientShallow, deepen);
  const parts: Buffer[] = [];
  for (const oid of plan.shallow) parts.push(pktLine(`shallow ${oid}\n`));
  for (const oid of plan.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
  parts.push(pktLine(haves.length === 0 ? 'NAK\n' : `ACK ${haves[haves.length - 1]}\n`));
  const pack = writePack(plan.objects);
  parts.push(...sidebandPackets(pack));
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

/** POST git-upload-pack: a v2 command request (ls-refs / fetch) or a v0 fetch. */
function handleUploadPack(repo: Repo, body: Buffer): Buffer {
  const { frames, rest } = decodePktFrames(body);
  const firstData = frames.find((frame) => frame.kind === 'data');
  const firstLine = firstData ? frameText(firstData) : '';

  if (firstLine.startsWith('command=')) {
    const command = firstLine.slice('command='.length);
    // Arguments are the data frames after the delim; capability lines sit before it.
    const delimIndex = frames.findIndex((frame) => frame.kind === 'delim');
    const argFrames = delimIndex === -1 ? [] : frames.slice(delimIndex + 1).filter((frame) => frame.kind === 'data');
    const args = argFrames.map(frameText);
    if (command === 'ls-refs') {
      const lsArgs: LsRefsArgs = { peel: false, symrefs: false, unborn: false, prefixes: [] };
      for (const arg of args) {
        if (arg === 'peel') lsArgs.peel = true;
        else if (arg === 'symrefs') lsArgs.symrefs = true;
        else if (arg === 'unborn') lsArgs.unborn = true;
        else if (arg.startsWith('ref-prefix ')) lsArgs.prefixes.push(arg.slice('ref-prefix '.length));
      }
      return handleLsRefs(repo, lsArgs);
    }
    if (command === 'fetch') {
      const wants: string[] = [];
      const haves: string[] = [];
      const clientShallow = new Set<string>();
      let deepen: number | null = null;
      let done = false;
      for (const arg of args) {
        if (arg.startsWith('want ')) wants.push(arg.slice(5).trim().toLowerCase());
        else if (arg.startsWith('have ')) haves.push(arg.slice(5).trim().toLowerCase());
        else if (arg.startsWith('shallow ')) clientShallow.add(arg.slice(8).trim().toLowerCase());
        else if (arg.startsWith('deepen ')) deepen = Number(arg.slice(7).trim());
        else if (arg === 'done') done = true;
      }
      return fetchResponseV2(repo, wants, haves, clientShallow, deepen, done);
    }
    throw new Error(`unsupported v2 command ${command}`);
  }

  // Protocol v0 fetch: want lines (capabilities ride the first), flush, shallow/deepen lines
  // may precede that flush in this client's encoding; haves and `done` follow it.
  void rest;
  const wants: string[] = [];
  const haves: string[] = [];
  const clientShallow = new Set<string>();
  let deepen: number | null = null;
  for (const frame of frames) {
    if (frame.kind !== 'data') continue;
    const line = frameText(frame);
    if (line.startsWith('want ')) wants.push(line.slice(5, 45).trim().toLowerCase());
    else if (line.startsWith('have ')) haves.push(line.slice(5).trim().toLowerCase());
    else if (line.startsWith('shallow ')) clientShallow.add(line.slice(8).trim().toLowerCase());
    else if (line.startsWith('deepen ')) deepen = Number(line.slice(7).trim());
  }
  return fetchResponseV0(repo, wants, haves, clientShallow, deepen);
}

interface PushCommand {
  oldOid: string;
  newOid: string;
  ref: string;
  capabilities: string[];
}

/** POST git-receive-pack: ingest the pack, validate each ref update, report status. */
async function handleReceivePack(repo: Repo, body: Buffer): Promise<Buffer> {
  const { frames, rest } = decodePktFrames(body);
  const commands: PushCommand[] = [];
  let capabilities: string[] = [];
  for (const frame of frames) {
    if (frame.kind !== 'data') continue;
    let line = frame.payload.toString('utf8');
    const nul = line.indexOf('\0');
    if (nul !== -1) {
      capabilities = line.slice(nul + 1).trim().split(/\s+/).filter((cap) => cap !== '');
      line = line.slice(0, nul);
    }
    const parts = line.trim().split(/\s+/);
    if (parts.length === 3 && isOid(parts[0] as string) && isOid(parts[1] as string)) {
      commands.push({
        oldOid: (parts[0] as string).toLowerCase(),
        newOid: (parts[1] as string).toLowerCase(),
        ref: parts[2] as string,
        capabilities,
      });
    }
  }

  let unpackOk = true;
  let unpackDetail = 'ok';
  if (rest.length > 0) {
    try {
      const entries = await parsePack(rest, (oid) => repo.objects.get(oid));
      for (const entry of entries) {
        if (!repo.objects.has(entry.oid)) repo.objects.set(entry.oid, { type: entry.type, data: entry.data });
      }
    } catch (err) {
      unpackOk = false;
      unpackDetail = err instanceof Error ? err.message : 'error';
    }
  } else if (commands.some((command) => command.newOid !== ZERO_OID && !repo.objects.has(command.newOid))) {
    // No pack at all is only well-formed for pure deletions; a create/update whose object is
    // already stored is still fine (checked per-ref below).
    unpackOk = true;
  }

  const reportLines: string[] = [unpackOk ? 'unpack ok' : `unpack ${unpackDetail}`];
  for (const command of commands) {
    const fail = (reason: string): void => {
      reportLines.push(`ng ${command.ref} ${reason}`);
    };
    if (!unpackOk) {
      fail('unpack failed');
      continue;
    }
    const current = repo.refs.get(command.ref) ?? ZERO_OID;
    if (command.newOid === ZERO_OID) {
      // Delete.
      if (command.oldOid !== current) {
        fail('stale info');
        continue;
      }
      repo.refs.delete(command.ref);
      reportLines.push(`ok ${command.ref}`);
      continue;
    }
    const newObject = repo.objects.get(command.newOid);
    if (!newObject) {
      fail('invalid object');
      continue;
    }
    if (command.oldOid === ZERO_OID) {
      if (current !== ZERO_OID) {
        fail('already exists');
        continue;
      }
    } else {
      if (command.oldOid !== current) {
        fail('stale info');
        continue;
      }
      if (
        command.ref.startsWith('refs/heads/') &&
        newObject.type === 'commit' &&
        repo.objects.get(command.oldOid)?.type === 'commit' &&
        !isAncestor(repo, command.oldOid, command.newOid)
      ) {
        fail('non-fast-forward');
        continue;
      }
    }
    repo.refs.set(command.ref, command.newOid);
    reportLines.push(`ok ${command.ref}`);
  }
  repo.updatedSec = stampNow().sec;

  const report = Buffer.concat([...reportLines.map((line) => pktLine(`${line}\n`)), PKT_FLUSH]);
  if (capabilities.includes('side-band-64k')) {
    return Buffer.concat([...sidebandPackets(report), PKT_FLUSH]);
  }
  return report;
}

// --------------------------------------------------------------------------- REST serialization

function userJson(login: string): Record<string, unknown> {
  return { login, id: 1000, type: 'User', site_admin: false };
}

function repoJson(repo: Repo): Record<string, unknown> {
  const owner = repo.owner ?? viewerLogin ?? '';
  return {
    id: repo.id,
    name: repo.name,
    full_name: `${owner}/${repo.name}`,
    owner: userJson(owner),
    private: repo.isPrivate,
    description: repo.description,
    fork: false,
    default_branch: repo.defaultBranch,
    created_at: isoOf(repo.createdSec),
    updated_at: isoOf(repo.updatedSec),
    pushed_at: isoOf(repo.updatedSec),
    size: 0,
    stargazers_count: 0,
    watchers_count: 0,
    forks_count: 0,
    open_issues_count: 0,
    visibility: repo.isPrivate ? 'private' : 'public',
  };
}

function labelJson(label: LabelRec): Record<string, unknown> {
  return { id: label.id, name: label.name, color: label.color, description: label.description, default: false };
}

function issueJson(repo: Repo, issue: IssueRec): Record<string, unknown> {
  return {
    id: issue.id,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels
      .map((name) => repo.labels.get(name))
      .filter((label): label is LabelRec => label !== undefined)
      .map(labelJson),
    user: userJson(viewerLogin ?? repo.owner ?? ''),
    comments: (repo.comments.get(issue.number) ?? []).length,
    created_at: isoOf(issue.createdSec),
    updated_at: isoOf(issue.updatedSec),
    closed_at: issue.state === 'closed' ? isoOf(issue.updatedSec) : null,
    pull_request: undefined,
  };
}

function commentJson(comment: CommentRec): Record<string, unknown> {
  return {
    id: comment.id,
    body: comment.body,
    user: userJson(viewerLogin ?? ''),
    created_at: isoOf(comment.createdSec),
    updated_at: isoOf(comment.updatedSec),
  };
}

function pullJson(repo: Repo, pull: PullRec): Record<string, unknown> {
  const headSha = repo.refs.get(`refs/heads/${pull.headRef}`) ?? pull.headShaAtCreate;
  const baseSha = repo.refs.get(`refs/heads/${pull.baseRef}`) ?? ZERO_OID;
  const side = (ref: string, sha: string): Record<string, unknown> => ({
    label: `${repo.owner ?? ''}:${ref}`,
    ref,
    sha,
    user: userJson(repo.owner ?? ''),
    repo: repoJson(repo),
  });
  return {
    id: pull.id,
    number: pull.number,
    state: pull.state,
    title: pull.title,
    body: pull.body,
    head: side(pull.headRef, headSha),
    base: side(pull.baseRef, baseSha),
    user: userJson(viewerLogin ?? repo.owner ?? ''),
    merged: pull.merged,
    merged_at: pull.mergedAtSec === null ? null : isoOf(pull.mergedAtSec),
    merge_commit_sha: pull.mergeCommitSha,
    created_at: isoOf(pull.createdSec),
    updated_at: isoOf(pull.updatedSec),
    closed_at: pull.state === 'closed' ? isoOf(pull.updatedSec) : null,
  };
}

function commitJson(repo: Repo, oid: string): Record<string, unknown> {
  const object = repo.objects.get(oid) as GitObject;
  const info = parseCommit(object.data);
  return {
    sha: oid,
    commit: {
      message: info.message,
      tree: { sha: info.tree },
      author: identJson(info.authorLine, info.timestamp),
      committer: identJson(info.committerLine, info.timestamp),
      comment_count: 0,
    },
    author: null,
    committer: null,
    parents: info.parents.map((parent) => ({ sha: parent })),
  };
}

// --------------------------------------------------------------------------- REST helpers

interface ApiResult {
  status: number;
  body?: unknown;
  headers?: Record<string, string>;
}

function apiError(status: number, message: string, extra?: Record<string, unknown>): ApiResult {
  return { status, body: { message, ...(extra ?? {}) } };
}

function parsePagination(query: URLSearchParams): { page: number; perPage: number } {
  const perPageRaw = Number(query.get('per_page') ?? '30');
  const pageRaw = Number(query.get('page') ?? '1');
  const perPage = Number.isFinite(perPageRaw) && perPageRaw > 0 ? Math.min(100, Math.trunc(perPageRaw)) : 30;
  const page = Number.isFinite(pageRaw) && pageRaw > 0 ? Math.trunc(pageRaw) : 1;
  return { page, perPage };
}

/** Slice one page and build the Link header (absolute, same origin) when more pages follow. */
function paginate<T>(items: T[], query: URLSearchParams, host: string, path: string): { page: T[]; headers: Record<string, string> } {
  const { page, perPage } = parsePagination(query);
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  const headers: Record<string, string> = {};
  if (start + perPage < items.length) {
    const lastPage = Math.ceil(items.length / perPage);
    const params = new URLSearchParams(query);
    params.set('page', String(page + 1));
    params.set('per_page', String(perPage));
    const nextUrl = `http://${host}${path}?${params.toString()}`;
    params.set('page', String(lastPage));
    const lastUrl = `http://${host}${path}?${params.toString()}`;
    headers.link = `<${nextUrl}>; rel="next", <${lastUrl}>; rel="last"`;
  }
  return { page: slice, headers };
}

// --------------------------------------------------------------------------- REST: repositories

function restCreateRepo(body: Record<string, unknown>): ApiResult {
  const name = typeof body.name === 'string' ? body.name : '';
  if (name === '' || !/^[A-Za-z0-9._-]+$/.test(name) || name === '.' || name === '..') {
    return apiError(422, 'Validation Failed', {
      errors: [{ resource: 'Repository', code: 'custom', field: 'name', message: 'name is not valid' }],
    });
  }
  if (reposByName.has(name)) {
    return apiError(422, 'Validation Failed', {
      errors: [{ resource: 'Repository', code: 'custom', field: 'name', message: 'name already exists on this account' }],
    });
  }
  const description = typeof body.description === 'string' ? body.description : null;
  const isPrivate = typeof body.private === 'boolean' ? body.private : false;
  const repo = createRepoRecord(name, description, isPrivate);
  if (body.auto_init === true) {
    const blob = storeObject(repo, 'blob', Buffer.from(`# ${name}\n`, 'utf8'));
    const tree = buildTreeFromFiles(repo, new Map([['README.md', { oid: blob, mode: '100644' }]]));
    const commit = makeCommit(repo, { tree, parent: null, message: 'Initial commit' });
    repo.refs.set(headRefOf(repo), commit);
  }
  return { status: 201, body: repoJson(repo) };
}

function restGetRepo(repo: Repo): ApiResult {
  return { status: 200, body: repoJson(repo) };
}

function restPatchRepo(repo: Repo, body: Record<string, unknown>): ApiResult {
  if (typeof body.description === 'string') repo.description = body.description;
  if (typeof body.private === 'boolean') repo.isPrivate = body.private;
  if (typeof body.default_branch === 'string' && repo.refs.has(`refs/heads/${body.default_branch}`)) {
    repo.defaultBranch = body.default_branch;
  }
  if (typeof body.name === 'string' && body.name !== repo.name && !reposByName.has(body.name)) {
    reposByName.delete(repo.name);
    repo.name = body.name;
    reposByName.set(repo.name, repo);
  }
  repo.updatedSec = stampNow().sec;
  return { status: 200, body: repoJson(repo) };
}

function restDeleteRepo(repo: Repo): ApiResult {
  reposByName.delete(repo.name);
  return { status: 204 };
}

function restListUserRepos(query: URLSearchParams, host: string, path: string): ApiResult {
  const all = [...reposByName.values()].sort((a, b) => a.id - b.id);
  const { page, headers } = paginate(all, query, host, path);
  return { status: 200, body: page.map(repoJson), headers };
}

function restListBranches(repo: Repo): ApiResult {
  const branches = [...repo.refs.entries()]
    .filter(([name]) => name.startsWith('refs/heads/'))
    .map(([name, oid]) => ({
      name: name.slice('refs/heads/'.length),
      commit: { sha: oid },
      protected: false,
    }))
    .sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
  return { status: 200, body: branches };
}

function restCreateRef(repo: Repo, body: Record<string, unknown>): ApiResult {
  const ref = typeof body.ref === 'string' ? body.ref : '';
  const sha = typeof body.sha === 'string' ? body.sha.toLowerCase() : '';
  if (!ref.startsWith('refs/') || !isOid(sha) || !repo.objects.has(sha)) {
    return apiError(422, 'Validation Failed', {
      errors: [{ resource: 'Reference', code: 'custom', field: 'sha', message: 'sha is not a known object' }],
    });
  }
  if (repo.refs.has(ref)) return apiError(422, 'Reference already exists');
  repo.refs.set(ref, sha);
  const object = repo.objects.get(sha) as GitObject;
  return { status: 201, body: { ref, object: { sha, type: object.type } } };
}

function restListCommits(repo: Repo, query: URLSearchParams): ApiResult {
  const refParam = query.get('sha') ?? repo.defaultBranch;
  const tip = resolveRefToCommit(repo, refParam);
  if (tip === null) return { status: 200, body: [] };
  const commits = ancestorsOf(repo, tip).map((oid) => commitJson(repo, oid));
  return { status: 200, body: commits };
}

// --------------------------------------------------------------------------- REST: contents

function resolveBranchTip(repo: Repo, branch: string | undefined): { ref: string; tip: string | null } {
  const ref = `refs/heads/${branch ?? repo.defaultBranch}`;
  return { ref, tip: repo.refs.get(ref) ?? null };
}

function restGetContents(repo: Repo, path: string, query: URLSearchParams): ApiResult {
  const refParam = query.get('ref') ?? undefined;
  let tip: string | null;
  if (refParam !== undefined) {
    tip = resolveRefToCommit(repo, refParam);
  } else {
    tip = repo.refs.get(headRefOf(repo)) ?? null;
  }
  if (tip === null) return apiError(404, 'Not Found');
  const map = treeMapOfCommit(repo, tip);
  const clean = path.replace(/^\/+|\/+$/g, '');
  if (clean !== '') {
    const entry = map.get(clean);
    if (entry && !entry.isDir) {
      const blob = repo.objects.get(entry.oid) as GitObject;
      return {
        status: 200,
        body: {
          type: 'file',
          encoding: 'base64',
          content: blob.data.toString('base64'),
          name: clean.split('/').pop(),
          path: clean,
          sha: entry.oid,
          size: blob.data.length,
        },
      };
    }
    if (entry && entry.isDir) {
      return { status: 200, body: directoryListing(map, clean) };
    }
    // A path that is a strict prefix of stored files is a directory even without a tree entry hit.
    const prefix = `${clean}/`;
    if ([...map.keys()].some((key) => key.startsWith(prefix))) {
      return { status: 200, body: directoryListing(map, clean) };
    }
    return apiError(404, 'Not Found');
  }
  return { status: 200, body: directoryListing(map, '') };
}

function directoryListing(map: Map<string, { oid: string; mode: string; isDir: boolean }>, dir: string): Record<string, unknown>[] {
  const prefix = dir === '' ? '' : `${dir}/`;
  const entries: Record<string, unknown>[] = [];
  for (const [path, entry] of map) {
    if (!path.startsWith(prefix)) continue;
    const rest = path.slice(prefix.length);
    if (rest.includes('/')) continue;
    entries.push({
      type: entry.isDir ? 'dir' : 'file',
      name: rest,
      path,
      sha: entry.oid,
      size: 0,
    });
  }
  entries.sort((a, b) => ((a.name as string) < (b.name as string) ? -1 : 1));
  return entries;
}

/** Apply a file-map change on a branch: rebuild the tree, commit, move the ref. */
function commitFileChange(
  repo: Repo,
  branchRef: string,
  tip: string | null,
  files: Map<string, { oid: string; mode: string }>,
  message: string,
): string {
  const tree = buildTreeFromFiles(repo, files);
  const commit = makeCommit(repo, { tree, parent: tip, message });
  repo.refs.set(branchRef, commit);
  repo.updatedSec = stampNow().sec;
  return commit;
}

function restPutContents(repo: Repo, path: string, body: Record<string, unknown>): ApiResult {
  const branch = typeof body.branch === 'string' ? body.branch : undefined;
  const { ref, tip } = resolveBranchTip(repo, branch);
  const message = typeof body.message === 'string' ? body.message : 'Update file';
  const contentB64 = typeof body.content === 'string' ? body.content : '';
  const data = Buffer.from(contentB64.replace(/\s+/g, ''), 'base64');
  const files = new Map<string, { oid: string; mode: string }>();
  if (tip !== null) {
    for (const [filePath, oid] of fileMapOfCommit(repo, tip)) files.set(filePath, { oid, mode: '100644' });
  }
  const existing = files.get(path);
  const providedSha = typeof body.sha === 'string' ? body.sha.toLowerCase() : undefined;
  if (existing !== undefined) {
    if (providedSha === undefined) return apiError(422, 'Validation Failed', { errors: [{ resource: 'Contents', code: 'missing_field', field: 'sha', message: 'sha is required when updating a file' }] });
    if (providedSha !== existing.oid) return apiError(409, 'Conflict: the file has changed since the sha was read');
  }
  const blobOid = storeObject(repo, 'blob', data);
  files.set(path, { oid: blobOid, mode: existing?.mode ?? '100644' });
  const commit = commitFileChange(repo, ref, tip, files, message);
  return {
    status: existing !== undefined ? 200 : 201,
    body: {
      content: { name: path.split('/').pop(), path, sha: blobOid, size: data.length, type: 'file', encoding: 'base64' },
      commit: { sha: commit, message },
    },
  };
}

function restDeleteContents(repo: Repo, path: string, body: Record<string, unknown>): ApiResult {
  const branch = typeof body.branch === 'string' ? body.branch : undefined;
  const { ref, tip } = resolveBranchTip(repo, branch);
  if (tip === null) return apiError(404, 'Not Found');
  const files = new Map<string, { oid: string; mode: string }>();
  for (const [filePath, oid] of fileMapOfCommit(repo, tip)) files.set(filePath, { oid, mode: '100644' });
  const existing = files.get(path);
  if (existing === undefined) return apiError(404, 'Not Found');
  const providedSha = typeof body.sha === 'string' ? body.sha.toLowerCase() : undefined;
  if (providedSha !== undefined && providedSha !== existing.oid) return apiError(409, 'Conflict: the file has changed since the sha was read');
  files.delete(path);
  const message = typeof body.message === 'string' ? body.message : 'Delete file';
  const commit = commitFileChange(repo, ref, tip, files, message);
  return { status: 200, body: { content: null, commit: { sha: commit, message } } };
}

// --------------------------------------------------------------------------- REST: labels, issues, comments

function restCreateLabel(repo: Repo, body: Record<string, unknown>): ApiResult {
  const name = typeof body.name === 'string' ? body.name : '';
  if (name === '') return apiError(422, 'Validation Failed');
  if (repo.labels.has(name)) return apiError(422, 'Validation Failed', { errors: [{ resource: 'Label', code: 'already_exists', field: 'name' }] });
  const label: LabelRec = {
    id: nextLabelId,
    name,
    color: typeof body.color === 'string' ? body.color.replace(/^#/, '') : 'ededed',
    description: typeof body.description === 'string' ? body.description : null,
  };
  nextLabelId += 1;
  repo.labels.set(name, label);
  return { status: 201, body: labelJson(label) };
}

function validateLabelNames(repo: Repo, labels: unknown): string[] | null {
  if (!Array.isArray(labels)) return [];
  const names: string[] = [];
  for (const entry of labels) {
    const name = typeof entry === 'string' ? entry : typeof (entry as Record<string, unknown>)?.name === 'string' ? ((entry as Record<string, unknown>).name as string) : '';
    if (name === '' || !repo.labels.has(name)) return null;
    names.push(name);
  }
  return names;
}

function restCreateIssue(repo: Repo, body: Record<string, unknown>): ApiResult {
  const title = typeof body.title === 'string' ? body.title : '';
  if (title === '') return apiError(422, 'Validation Failed', { errors: [{ resource: 'Issue', code: 'missing_field', field: 'title' }] });
  const labels = validateLabelNames(repo, body.labels);
  if (labels === null) return apiError(422, 'Validation Failed', { errors: [{ resource: 'Issue', code: 'custom', field: 'labels', message: 'labels contain an unknown label' }] });
  const stamp = stampNow();
  const issue: IssueRec = {
    id: nextIssueId,
    number: repo.nextNumber,
    title,
    body: typeof body.body === 'string' ? body.body : '',
    state: 'open',
    labels,
    createdSec: stamp.sec,
    updatedSec: stamp.sec,
  };
  nextIssueId += 1;
  repo.nextNumber += 1;
  repo.issues.set(issue.number, issue);
  return { status: 201, body: issueJson(repo, issue) };
}

function restListIssues(repo: Repo, query: URLSearchParams, host: string, path: string): ApiResult {
  const state = query.get('state') ?? 'open';
  let issues = [...repo.issues.values()];
  if (state === 'open' || state === 'closed') issues = issues.filter((issue) => issue.state === state);
  const direction = query.get('direction') ?? 'desc';
  issues.sort((a, b) => (direction === 'asc' ? a.number - b.number : b.number - a.number));
  const { page, headers } = paginate(issues, query, host, path);
  return { status: 200, body: page.map((issue) => issueJson(repo, issue)), headers };
}

function restGetIssue(repo: Repo, number: number): ApiResult {
  const issue = repo.issues.get(number);
  if (!issue) return apiError(404, 'Not Found');
  return { status: 200, body: issueJson(repo, issue) };
}

function restPatchIssue(repo: Repo, number: number, body: Record<string, unknown>): ApiResult {
  const issue = repo.issues.get(number);
  if (!issue) return apiError(404, 'Not Found');
  if (typeof body.title === 'string') issue.title = body.title;
  if (typeof body.body === 'string') issue.body = body.body;
  if (body.state === 'open' || body.state === 'closed') issue.state = body.state;
  if (body.labels !== undefined) {
    const labels = validateLabelNames(repo, body.labels);
    if (labels === null) return apiError(422, 'Validation Failed');
    issue.labels = labels;
  }
  issue.updatedSec = stampNow().sec;
  return { status: 200, body: issueJson(repo, issue) };
}

function restCreateComment(repo: Repo, number: number, body: Record<string, unknown>): ApiResult {
  const issue = repo.issues.get(number);
  if (!issue) return apiError(404, 'Not Found');
  const stamp = stampNow();
  const comment: CommentRec = {
    id: nextCommentId,
    issueNumber: number,
    body: typeof body.body === 'string' ? body.body : '',
    createdSec: stamp.sec,
    updatedSec: stamp.sec,
  };
  nextCommentId += 1;
  const list = repo.comments.get(number) ?? [];
  list.push(comment);
  repo.comments.set(number, list);
  return { status: 201, body: commentJson(comment) };
}

function restListComments(repo: Repo, number: number): ApiResult {
  const issue = repo.issues.get(number);
  if (!issue) return apiError(404, 'Not Found');
  return { status: 200, body: (repo.comments.get(number) ?? []).map(commentJson) };
}

// --------------------------------------------------------------------------- REST: pull requests

function restCreatePull(repo: Repo, body: Record<string, unknown>): ApiResult {
  const head = typeof body.head === 'string' ? body.head : '';
  const base = typeof body.base === 'string' ? body.base : '';
  const headTip = repo.refs.get(`refs/heads/${head}`);
  const baseTip = repo.refs.get(`refs/heads/${base}`);
  if (headTip === undefined || baseTip === undefined) {
    return apiError(422, 'Validation Failed', { errors: [{ resource: 'PullRequest', code: 'custom', message: 'head or base branch does not exist' }] });
  }
  const stamp = stampNow();
  const pull: PullRec = {
    id: nextPullId,
    number: repo.nextNumber,
    title: typeof body.title === 'string' ? body.title : '',
    body: typeof body.body === 'string' ? body.body : '',
    state: 'open',
    headRef: head,
    baseRef: base,
    headShaAtCreate: headTip,
    merged: false,
    mergedAtSec: null,
    mergeCommitSha: null,
    createdSec: stamp.sec,
    updatedSec: stamp.sec,
  };
  nextPullId += 1;
  repo.nextNumber += 1;
  repo.pulls.set(pull.number, pull);
  return { status: 201, body: pullJson(repo, pull) };
}

function restListPulls(repo: Repo, query: URLSearchParams, host: string, path: string): ApiResult {
  const state = query.get('state') ?? 'open';
  let pulls = [...repo.pulls.values()];
  if (state === 'open' || state === 'closed') pulls = pulls.filter((pull) => pull.state === state);
  pulls.sort((a, b) => b.number - a.number);
  const { page, headers } = paginate(pulls, query, host, path);
  return { status: 200, body: page.map((pull) => pullJson(repo, pull)), headers };
}

function restGetPull(repo: Repo, number: number): ApiResult {
  const pull = repo.pulls.get(number);
  if (!pull) return apiError(404, 'Not Found');
  return { status: 200, body: pullJson(repo, pull) };
}

/** Line-diff counts between two blob contents (LCS; coarse fallback for very large files). */
function lineDiffCounts(oldText: string, newText: string): { additions: number; deletions: number } {
  const splitLines = (text: string): string[] => {
    const lines = text.split('\n');
    if (lines.length > 0 && lines[lines.length - 1] === '') lines.pop();
    return lines;
  };
  const oldLines = splitLines(oldText);
  const newLines = splitLines(newText);
  if (oldLines.length * newLines.length > 4_000_000) {
    return { additions: newLines.length, deletions: oldLines.length };
  }
  const dp: number[] = new Array(newLines.length + 1).fill(0);
  for (let i = oldLines.length - 1; i >= 0; i -= 1) {
    let prevDiag = 0;
    for (let j = newLines.length - 1; j >= 0; j -= 1) {
      const saved = dp[j] as number;
      dp[j] = oldLines[i] === newLines[j] ? prevDiag + 1 : Math.max(dp[j] as number, dp[j + 1] as number);
      prevDiag = saved;
    }
  }
  const common = dp[0] as number;
  return { additions: newLines.length - common, deletions: oldLines.length - common };
}

function restPullFiles(repo: Repo, number: number): ApiResult {
  const pull = repo.pulls.get(number);
  if (!pull) return apiError(404, 'Not Found');
  const headTip = repo.refs.get(`refs/heads/${pull.headRef}`) ?? pull.headShaAtCreate;
  const baseTip = repo.refs.get(`refs/heads/${pull.baseRef}`);
  if (baseTip === undefined) return { status: 200, body: [] };
  const base = mergeBase(repo, baseTip, headTip) ?? baseTip;
  const baseFiles = fileMapOfCommit(repo, base);
  const headFiles = fileMapOfCommit(repo, headTip);
  const paths = new Set<string>([...baseFiles.keys(), ...headFiles.keys()]);
  const files: Record<string, unknown>[] = [];
  for (const path of [...paths].sort()) {
    const oldOid = baseFiles.get(path);
    const newOid = headFiles.get(path);
    if (oldOid === newOid) continue;
    const oldText = oldOid === undefined ? '' : (repo.objects.get(oldOid)?.data.toString('utf8') ?? '');
    const newText = newOid === undefined ? '' : (repo.objects.get(newOid)?.data.toString('utf8') ?? '');
    const { additions, deletions } = lineDiffCounts(oldText, newText);
    files.push({
      filename: path,
      status: oldOid === undefined ? 'added' : newOid === undefined ? 'removed' : 'modified',
      additions,
      deletions,
      changes: additions + deletions,
      sha: newOid ?? oldOid,
    });
  }
  return { status: 200, body: files };
}

function restMergePull(repo: Repo, number: number, body: Record<string, unknown>): ApiResult {
  const pull = repo.pulls.get(number);
  if (!pull) return apiError(404, 'Not Found');
  if (pull.state !== 'open' || pull.merged) return apiError(405, 'Pull Request is not mergeable');
  const baseRef = `refs/heads/${pull.baseRef}`;
  const baseTip = repo.refs.get(baseRef);
  const headTip = repo.refs.get(`refs/heads/${pull.headRef}`) ?? pull.headShaAtCreate;
  if (baseTip === undefined) return apiError(405, 'Pull Request is not mergeable');
  const base = mergeBase(repo, baseTip, headTip);
  const originFiles = base === null ? new Map<string, string>() : fileMapOfCommit(repo, base);
  const baseFiles = fileMapOfCommit(repo, baseTip);
  const headFiles = fileMapOfCommit(repo, headTip);
  const mergedFiles = new Map<string, { oid: string; mode: string }>();
  const paths = new Set<string>([...originFiles.keys(), ...baseFiles.keys(), ...headFiles.keys()]);
  for (const path of paths) {
    const origin = originFiles.get(path);
    const baseVersion = baseFiles.get(path);
    const headVersion = headFiles.get(path);
    let winner: string | undefined;
    if (headVersion === origin) winner = baseVersion;
    else if (baseVersion === origin) winner = headVersion;
    else if (baseVersion === headVersion) winner = baseVersion;
    else return apiError(405, 'Pull Request is not mergeable: the head and base have conflicting changes');
    if (winner !== undefined) mergedFiles.set(path, { oid: winner, mode: '100644' });
  }
  const tree = buildTreeFromFiles(repo, mergedFiles);
  const method = typeof body.merge_method === 'string' ? body.merge_method : 'merge';
  const stamp = stampNow();
  const message =
    method === 'squash'
      ? `${pull.title} (#${pull.number})${pull.body === '' ? '' : `\n\n${pull.body}`}`
      : `Merge pull request #${pull.number} from ${pull.headRef}`;
  const commitData = buildCommit({
    tree,
    parents: method === 'merge' ? [baseTip, headTip] : [baseTip],
    message,
    authorName: COMMITTER.name,
    authorEmail: COMMITTER.email,
    timestamp: stamp.sec,
  });
  const commit = storeObject(repo, 'commit', commitData);
  repo.refs.set(baseRef, commit);
  pull.state = 'closed';
  pull.merged = true;
  pull.mergedAtSec = stamp.sec;
  pull.mergeCommitSha = commit;
  pull.updatedSec = stamp.sec;
  repo.updatedSec = stamp.sec;
  return { status: 200, body: { sha: commit, merged: true, message: 'Pull Request successfully merged' } };
}

// --------------------------------------------------------------------------- GraphQL (v4)
//
// A small hand-written GraphQL engine (tokenizer, parser, executor) over the same in-memory
// store the REST surface uses, serving the documents gh and github-mcp-server send. Global ids
// are base64 "Type:numericId" — opaque, stable across reads, and decodable by node(id:).

// ---- global ids

function gqlId(type: string, numericId: number): string {
  return Buffer.from(`${type}:${numericId}`, 'utf8').toString('base64');
}

function parseGqlId(id: string): { type: string; numericId: number } | null {
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const match = /^([A-Za-z]+):(\d+)$/.exec(text);
    if (!match) return null;
    return { type: match[1] as string, numericId: Number(match[2]) };
  } catch {
    return null;
  }
}

function repoByGqlId(id: string): Repo | null {
  const parsed = parseGqlId(id);
  if (parsed === null || parsed.type !== 'Repository') return null;
  for (const repo of reposByName.values()) if (repo.id === parsed.numericId) return repo;
  return null;
}

function issueByGqlId(id: string): { repo: Repo; issue: IssueRec } | null {
  const parsed = parseGqlId(id);
  if (parsed === null || parsed.type !== 'Issue') return null;
  for (const repo of reposByName.values()) {
    for (const issue of repo.issues.values()) if (issue.id === parsed.numericId) return { repo, issue };
  }
  return null;
}

function pullByGqlId(id: string): { repo: Repo; pull: PullRec } | null {
  const parsed = parseGqlId(id);
  if (parsed === null || parsed.type !== 'PullRequest') return null;
  for (const repo of reposByName.values()) {
    for (const pull of repo.pulls.values()) if (pull.id === parsed.numericId) return { repo, pull };
  }
  return null;
}

function commentByGqlId(id: string): { repo: Repo; issueNumber: number; comment: CommentRec } | null {
  const parsed = parseGqlId(id);
  if (parsed === null || parsed.type !== 'IssueComment') return null;
  for (const repo of reposByName.values()) {
    for (const [issueNumber, comments] of repo.comments) {
      for (const comment of comments) if (comment.id === parsed.numericId) return { repo, issueNumber, comment };
    }
  }
  return null;
}

// ---- tokenizer

interface GqlToken {
  type: string;
  value: string;
}

function gqlTokenize(source: string): GqlToken[] {
  const tokens: GqlToken[] = [];
  let i = 0;
  while (i < source.length) {
    const c = source[i] as string;
    if (c === ' ' || c === '\t' || c === '\n' || c === '\r' || c === ',' || c === '\uFEFF') {
      i += 1;
      continue;
    }
    if (c === '#') {
      while (i < source.length && source[i] !== '\n') i += 1;
      continue;
    }
    if (source.startsWith('...', i)) {
      tokens.push({ type: '...', value: '...' });
      i += 3;
      continue;
    }
    if ('!$():=@[]{}|&'.includes(c)) {
      tokens.push({ type: c, value: c });
      i += 1;
      continue;
    }
    if (c === '"') {
      if (source.startsWith('"""', i)) {
        const end = source.indexOf('"""', i + 3);
        tokens.push({ type: 'string', value: source.slice(i + 3, end === -1 ? source.length : end) });
        i = end === -1 ? source.length : end + 3;
        continue;
      }
      let j = i + 1;
      let out = '';
      while (j < source.length && source[j] !== '"') {
        if (source[j] === '\\') {
          const esc = source[j + 1] as string;
          if (esc === 'u') {
            out += String.fromCharCode(parseInt(source.slice(j + 2, j + 6), 16));
            j += 6;
          } else {
            const table: Record<string, string> = { n: '\n', t: '\t', r: '\r', b: '\b', f: '\f', '/': '/', '\\': '\\', '"': '"' };
            out += table[esc] ?? esc;
            j += 2;
          }
        } else {
          out += source[j];
          j += 1;
        }
      }
      tokens.push({ type: 'string', value: out });
      i = j + 1;
      continue;
    }
    if (/[-0-9]/.test(c)) {
      let j = i;
      while (j < source.length && /[-0-9.eE+]/.test(source[j] as string)) j += 1;
      const text = source.slice(i, j);
      tokens.push({ type: /[.eE]/.test(text) ? 'float' : 'int', value: text });
      i = j;
      continue;
    }
    if (/[_A-Za-z]/.test(c)) {
      let j = i;
      while (j < source.length && /[_0-9A-Za-z]/.test(source[j] as string)) j += 1;
      tokens.push({ type: 'name', value: source.slice(i, j) });
      i = j;
      continue;
    }
    throw new Error(`GraphQL syntax error: unexpected character ${JSON.stringify(c)}`);
  }
  tokens.push({ type: 'eof', value: '' });
  return tokens;
}

// ---- parser

type GqlValue =
  | { kind: 'variable'; name: string }
  | { kind: 'string'; value: string }
  | { kind: 'int'; value: number }
  | { kind: 'float'; value: number }
  | { kind: 'boolean'; value: boolean }
  | { kind: 'null' }
  | { kind: 'enum'; value: string }
  | { kind: 'list'; values: GqlValue[] }
  | { kind: 'object'; fields: { name: string; value: GqlValue }[] };

type GqlSelection =
  | {
      kind: 'field';
      alias: string | null;
      name: string;
      args: { name: string; value: GqlValue }[];
      selectionSet: GqlSelection[] | null;
    }
  | { kind: 'inline'; typeCondition: string | null; selectionSet: GqlSelection[] }
  | { kind: 'spread'; name: string };

interface GqlOperation {
  operation: 'query' | 'mutation';
  name: string | null;
  selectionSet: GqlSelection[];
}

interface GqlDocument {
  operations: GqlOperation[];
  fragments: Map<string, { typeCondition: string | null; selectionSet: GqlSelection[] }>;
}

class GqlParser {
  private readonly tokens: GqlToken[];
  private pos = 0;

  constructor(source: string) {
    this.tokens = gqlTokenize(source);
  }

  private peek(): GqlToken {
    return this.tokens[this.pos] as GqlToken;
  }

  private next(): GqlToken {
    const token = this.tokens[this.pos] as GqlToken;
    this.pos += 1;
    return token;
  }

  private expect(type: string): GqlToken {
    const token = this.next();
    if (token.type !== type) throw new Error(`GraphQL syntax error: expected ${type}, got ${token.type} ${JSON.stringify(token.value)}`);
    return token;
  }

  private skipDirectives(): void {
    while (this.peek().type === '@') {
      this.next();
      this.expect('name');
      if (this.peek().type === '(') this.parseArguments();
    }
  }

  private parseArguments(): { name: string; value: GqlValue }[] {
    const args: { name: string; value: GqlValue }[] = [];
    this.expect('(');
    while (this.peek().type !== ')') {
      const name = this.expect('name').value;
      this.expect(':');
      args.push({ name, value: this.parseValue() });
    }
    this.expect(')');
    return args;
  }

  private parseValue(): GqlValue {
    const token = this.next();
    if (token.type === '$') return { kind: 'variable', name: this.expect('name').value };
    if (token.type === 'string') return { kind: 'string', value: token.value };
    if (token.type === 'int') return { kind: 'int', value: Number(token.value) };
    if (token.type === 'float') return { kind: 'float', value: Number(token.value) };
    if (token.type === '[') {
      const values: GqlValue[] = [];
      while (this.peek().type !== ']') values.push(this.parseValue());
      this.expect(']');
      return { kind: 'list', values };
    }
    if (token.type === '{') {
      const fields: { name: string; value: GqlValue }[] = [];
      while (this.peek().type !== '}') {
        const name = this.expect('name').value;
        this.expect(':');
        fields.push({ name, value: this.parseValue() });
      }
      this.expect('}');
      return { kind: 'object', fields };
    }
    if (token.type === 'name') {
      if (token.value === 'true') return { kind: 'boolean', value: true };
      if (token.value === 'false') return { kind: 'boolean', value: false };
      if (token.value === 'null') return { kind: 'null' };
      return { kind: 'enum', value: token.value };
    }
    throw new Error(`GraphQL syntax error: unexpected value token ${token.type}`);
  }

  private skipTypeRef(): void {
    if (this.peek().type === '[') {
      this.next();
      this.skipTypeRef();
      this.expect(']');
    } else {
      this.expect('name');
    }
    if (this.peek().type === '!') this.next();
  }

  private parseVariableDefinitions(): void {
    this.expect('(');
    while (this.peek().type !== ')') {
      this.expect('$');
      this.expect('name');
      this.expect(':');
      this.skipTypeRef();
      if (this.peek().type === '=') {
        this.next();
        this.parseValue(); // a default value; the checks always pass variables explicitly
      }
      this.skipDirectives();
    }
    this.expect(')');
  }

  private parseSelectionSet(): GqlSelection[] {
    const selections: GqlSelection[] = [];
    this.expect('{');
    while (this.peek().type !== '}') selections.push(this.parseSelection());
    this.expect('}');
    return selections;
  }

  private parseSelection(): GqlSelection {
    if (this.peek().type === '...') {
      this.next();
      if (this.peek().type === '{') return { kind: 'inline', typeCondition: null, selectionSet: this.parseSelectionSet() };
      const name = this.expect('name').value;
      if (name === 'on') {
        const typeCondition = this.expect('name').value;
        this.skipDirectives();
        return { kind: 'inline', typeCondition, selectionSet: this.parseSelectionSet() };
      }
      this.skipDirectives();
      return { kind: 'spread', name };
    }
    let name = this.expect('name').value;
    let alias: string | null = null;
    if (this.peek().type === ':') {
      this.next();
      alias = name;
      name = this.expect('name').value;
    }
    const args = this.peek().type === '(' ? this.parseArguments() : [];
    this.skipDirectives();
    const selectionSet = this.peek().type === '{' ? this.parseSelectionSet() : null;
    return { kind: 'field', alias, name, args, selectionSet };
  }

  parseDocument(): GqlDocument {
    const operations: GqlOperation[] = [];
    const fragments = new Map<string, { typeCondition: string | null; selectionSet: GqlSelection[] }>();
    while (this.peek().type !== 'eof') {
      if (this.peek().type === '{') {
        operations.push({ operation: 'query', name: null, selectionSet: this.parseSelectionSet() });
        continue;
      }
      const keyword = this.expect('name').value;
      if (keyword === 'query' || keyword === 'mutation' || keyword === 'subscription') {
        let name: string | null = null;
        if (this.peek().type === 'name') name = this.next().value;
        if (this.peek().type === '(') this.parseVariableDefinitions();
        this.skipDirectives();
        operations.push({
          operation: keyword === 'mutation' ? 'mutation' : 'query',
          name,
          selectionSet: this.parseSelectionSet(),
        });
        continue;
      }
      if (keyword === 'fragment') {
        const name = this.expect('name').value;
        const on = this.expect('name').value;
        if (on !== 'on') throw new Error(`GraphQL syntax error: expected "on" in fragment ${name}`);
        const typeCondition = this.expect('name').value;
        this.skipDirectives();
        fragments.set(name, { typeCondition, selectionSet: this.parseSelectionSet() });
        continue;
      }
      throw new Error(`GraphQL syntax error: unexpected definition ${JSON.stringify(keyword)}`);
    }
    return { operations, fragments };
  }
}

// ---- schema (the introspection view)

const GQL_ENUM_VALUES: Record<string, string[]> = {
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  PullRequestMergeMethod: ['MERGE', 'SQUASH', 'REBASE'],
  RepositoryPermission: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'],
  SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION'],
  IssueOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'],
  OrderDirection: ['ASC', 'DESC'],
  CommentAuthorAssociation: ['OWNER', 'MEMBER', 'COLLABORATOR', 'CONTRIBUTOR', 'FIRST_TIME_CONTRIBUTOR', 'FIRST_TIMER', 'NONE', 'MANNEQUIN'],
  MergeStateStatus: ['BEHIND', 'BLOCKED', 'CLEAN', 'DIRTY', 'DRAFT', 'HAS_HOOKS', 'UNKNOWN', 'UNSTABLE'],
  RequestableCheckStatusState: ['COMPLETED', 'IN_PROGRESS', 'PENDING', 'QUEUED', 'WAITING'],
  StatusState: ['ERROR', 'EXPECTED', 'FAILURE', 'PENDING', 'SUCCESS'],
  FileStatus: ['ADDED', 'CHANGED', 'COPIED', 'DELETED', 'MODIFIED', 'RENAMED', 'UNCHANGED'],
};

const GQL_TYPE_FIELDS: Record<string, string[]> = {
  Query: ['viewer', 'repository', 'node', 'nodes', 'search', 'rateLimit', 'meta', 'organization', 'user'],
  Mutation: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment', 'updateIssue', 'createRepository'],
  User: ['id', 'login', 'name', 'email', 'url', 'avatarUrl', 'createdAt', 'updatedAt', 'isViewer', 'databaseId'],
  Repository: [
    'id', 'databaseId', 'name', 'nameWithOwner', 'description', 'isPrivate', 'isFork', 'isArchived', 'isDisabled', 'isEmpty',
    'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'hasProjectsEnabled', 'hasWikiEnabled', 'hasDiscussionsEnabled',
    'issue', 'issues', 'pullRequest', 'pullRequests', 'createdAt', 'updatedAt', 'pushedAt', 'url', 'sshUrl', 'stargazerCount',
    'forkCount', 'watchers', 'primaryLanguage', 'licenseInfo', 'refs', 'ref', 'branchProtectionRules', 'collaborators', 'labels', 'milestones',
  ],
  Ref: ['id', 'name', 'prefix', 'target', 'repository'],
  Issue: [
    'id', 'databaseId', 'number', 'title', 'state', 'body', 'bodyText', 'bodyHTML', 'author', 'editor', 'repository', 'labels',
    'comments', 'assignees', 'milestone', 'createdAt', 'updatedAt', 'closedAt', 'closed', 'url', 'viewerCanUpdate', 'viewerCanDelete',
    'viewerDidAuthor', 'locked', 'activeLockReason', 'reactionGroups', 'participants', 'timelineItems', 'stateReason',
  ],
  IssueConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  IssueEdge: ['node', 'cursor'],
  PageInfo: ['hasNextPage', 'hasPreviousPage', 'startCursor', 'endCursor'],
  PullRequest: [
    'id', 'databaseId', 'number', 'title', 'state', 'body', 'bodyText', 'author', 'editor', 'repository', 'merged', 'mergedAt',
    'mergeable', 'headRefName', 'baseRefName', 'headRef', 'baseRef', 'headRepository', 'baseRepository', 'files', 'commits',
    'comments', 'reviews', 'labels', 'assignees', 'createdAt', 'updatedAt', 'closedAt', 'closed', 'url', 'additions', 'deletions',
    'changedFiles', 'mergeCommit', 'potentialMergeCommit', 'isDraft', 'viewerCanUpdate', 'maintainerCanModify', 'mergeStateStatus',
  ],
  PullRequestConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestEdge: ['node', 'cursor'],
  PullRequestChangedFile: ['path', 'additions', 'deletions', 'changeType'],
  PullRequestChangedFileConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  IssueComment: ['id', 'databaseId', 'body', 'bodyText', 'author', 'editor', 'createdAt', 'updatedAt', 'url', 'issue', 'repository', 'viewerCanUpdate', 'viewerCanDelete'],
  IssueCommentConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  CommentEdge: ['node', 'cursor'],
  Label: ['id', 'name', 'color', 'description', 'isDefault', 'url'],
  UserConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestCommitConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestReviewConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  LabelConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  CreateIssuePayload: ['clientMutationId', 'issue'],
  CloseIssuePayload: ['clientMutationId', 'issue'],
  CreatePullRequestPayload: ['clientMutationId', 'pullRequest'],
  MergePullRequestPayload: ['clientMutationId', 'pullRequest'],
  AddCommentPayload: ['clientMutationId', 'commentEdge', 'subject'],
  Node: ['id'],
  SearchResultItemConnection: ['nodes', 'edges', 'pageInfo', 'issueCount', 'repositoryCount', 'userCount', 'discussionCount', 'codeCount'],
  __Type: ['name', 'kind', 'description', 'fields', 'enumValues', 'possibleTypes', 'inputFields', 'ofType', 'specifiedByURL', 'interfaces'],
  __Field: ['name', 'description', 'args', 'type', 'isDeprecated', 'deprecationReason'],
  __EnumValue: ['name', 'description', 'isDeprecated', 'deprecationReason'],
  __InputValue: ['name', 'description', 'type', 'defaultValue', 'isDeprecated', 'deprecationReason'],
  __Schema: ['types', 'queryType', 'mutationType', 'subscriptionType', 'directives', 'description'],
  __Directive: ['name', 'description', 'locations', 'args', 'isRepeatable'],
};

const GQL_TYPE_KINDS: Record<string, string> = (() => {
  const kinds: Record<string, string> = {};
  for (const name of Object.keys(GQL_TYPE_FIELDS)) kinds[name] = name === 'Node' ? 'INTERFACE' : 'OBJECT';
  for (const name of Object.keys(GQL_ENUM_VALUES)) kinds[name] = 'ENUM';
  for (const name of ['String', 'Int', 'Float', 'Boolean', 'ID', 'DateTime', 'URI', 'HTML', 'GitObjectID', 'Base64String', 'GitTimestamp', 'PreciseDateTime', 'X509Certificate', 'GitSSHRemote']) kinds[name] = 'SCALAR';
  for (const name of ['CreateIssueInput', 'CloseIssueInput', 'CreatePullRequestInput', 'MergePullRequestInput', 'AddCommentInput', 'IssueOrder', 'UpdateIssueInput', 'CreateRepositoryInput']) kinds[name] = 'INPUT_OBJECT';
  return kinds;
})();

// ---- executor

type GqlObj = { __typename: string; [key: string]: unknown };
type GqlResolver = (source: GqlObj, args: Record<string, unknown>, ctx: GqlExecCtx) => unknown;

interface GqlErrorEntry {
  message: string;
  path?: (string | number)[];
}

interface GqlExecCtx {
  variables: Record<string, unknown>;
  fragments: Map<string, { typeCondition: string | null; selectionSet: GqlSelection[] }>;
  errors: GqlErrorEntry[];
}

class GqlFieldError extends Error {}

function gqlUserObj(login: string): GqlObj {
  return { __typename: 'User', login };
}

function gqlRepoObj(repo: Repo): GqlObj {
  return { __typename: 'Repository', repo };
}

function gqlIssueObj(repo: Repo, issue: IssueRec): GqlObj {
  return { __typename: 'Issue', repo, issue };
}

function gqlPullObj(repo: Repo, pull: PullRec): GqlObj {
  return { __typename: 'PullRequest', repo, pull };
}

function gqlCommentObj(repo: Repo, issueNumber: number, comment: CommentRec): GqlObj {
  return { __typename: 'IssueComment', repo, issueNumber, comment };
}

function gqlCursorFor(number: number): string {
  return Buffer.from(`issue-cursor:${number}`, 'utf8').toString('base64');
}

function gqlNumberFromCursor(cursor: string): number | null {
  try {
    const match = /^issue-cursor:(\d+)$/.exec(Buffer.from(cursor, 'base64').toString('utf8'));
    return match ? Number(match[1]) : null;
  } catch {
    return null;
  }
}

/** The changed files of a pull request (merge-base view, as the REST files route computes). */
function pullChangedFiles(repo: Repo, pull: PullRec): { path: string; additions: number; deletions: number; status: string }[] {
  const headTip = repo.refs.get(`refs/heads/${pull.headRef}`) ?? pull.headShaAtCreate;
  const baseTip = repo.refs.get(`refs/heads/${pull.baseRef}`);
  if (baseTip === undefined) return [];
  const base = mergeBase(repo, baseTip, headTip) ?? baseTip;
  const baseFiles = fileMapOfCommit(repo, base);
  const headFiles = fileMapOfCommit(repo, headTip);
  const paths = new Set<string>([...baseFiles.keys(), ...headFiles.keys()]);
  const files: { path: string; additions: number; deletions: number; status: string }[] = [];
  for (const path of [...paths].sort()) {
    const oldOid = baseFiles.get(path);
    const newOid = headFiles.get(path);
    if (oldOid === newOid) continue;
    const oldText = oldOid === undefined ? '' : (repo.objects.get(oldOid)?.data.toString('utf8') ?? '');
    const newText = newOid === undefined ? '' : (repo.objects.get(newOid)?.data.toString('utf8') ?? '');
    const { additions, deletions } = lineDiffCounts(oldText, newText);
    files.push({ path, additions, deletions, status: oldOid === undefined ? 'added' : newOid === undefined ? 'removed' : 'modified' });
  }
  return files;
}

/** MERGEABLE / CONFLICTING by the same per-path three-way test the merge applies; UNKNOWN once merged or closed. */
function pullMergeableState(repo: Repo, pull: PullRec): string {
  if (pull.merged || pull.state !== 'open') return 'UNKNOWN';
  const baseTip = repo.refs.get(`refs/heads/${pull.baseRef}`);
  const headTip = repo.refs.get(`refs/heads/${pull.headRef}`) ?? pull.headShaAtCreate;
  if (baseTip === undefined) return 'UNKNOWN';
  const base = mergeBase(repo, baseTip, headTip);
  const originFiles = base === null ? new Map<string, string>() : fileMapOfCommit(repo, base);
  const baseFiles = fileMapOfCommit(repo, baseTip);
  const headFiles = fileMapOfCommit(repo, headTip);
  const paths = new Set<string>([...originFiles.keys(), ...baseFiles.keys(), ...headFiles.keys()]);
  for (const path of paths) {
    const origin = originFiles.get(path);
    const baseVersion = baseFiles.get(path);
    const headVersion = headFiles.get(path);
    if (headVersion === origin || baseVersion === origin || baseVersion === headVersion) continue;
    return 'CONFLICTING';
  }
  return 'MERGEABLE';
}

function gqlIssuesConnection(repo: Repo, args: Record<string, unknown>): GqlObj {
  let list = [...repo.issues.values()];
  if (Array.isArray(args.states)) {
    const states = args.states.map((entry) => String(entry));
    list = list.filter((issue) => states.includes(issue.state.toUpperCase()));
  }
  const orderBy = (typeof args.orderBy === 'object' && args.orderBy !== null ? args.orderBy : {}) as Record<string, unknown>;
  const field = typeof orderBy.field === 'string' ? orderBy.field : 'CREATED_AT';
  const direction = typeof orderBy.direction === 'string' ? orderBy.direction : 'ASC';
  list.sort((a, b) => {
    let cmp: number;
    if (field === 'COMMENTS') cmp = (repo.comments.get(a.number)?.length ?? 0) - (repo.comments.get(b.number)?.length ?? 0) || a.number - b.number;
    else if (field === 'UPDATED_AT') cmp = a.updatedSec - b.updatedSec || a.number - b.number;
    else cmp = a.number - b.number;
    return direction === 'DESC' ? -cmp : cmp;
  });
  let start = 0;
  if (typeof args.after === 'string' && args.after !== '') {
    const number = gqlNumberFromCursor(args.after);
    const index = number === null ? -1 : list.findIndex((issue) => issue.number === number);
    if (index >= 0) start = index + 1;
  }
  const first = typeof args.first === 'number' && Number.isFinite(args.first) ? Math.max(0, Math.trunc(args.first)) : 30;
  const slice = list.slice(start, start + first);
  const nodes = slice.map((issue) => gqlIssueObj(repo, issue));
  return {
    __typename: 'IssueConnection',
    nodes,
    edges: slice.map((issue) => ({ __typename: 'IssueEdge', node: gqlIssueObj(repo, issue), cursor: gqlCursorFor(issue.number) })),
    pageInfo: {
      __typename: 'PageInfo',
      hasNextPage: start + slice.length < list.length,
      hasPreviousPage: start > 0,
      startCursor: slice.length > 0 ? gqlCursorFor((slice[0] as IssueRec).number) : null,
      endCursor: slice.length > 0 ? gqlCursorFor((slice[slice.length - 1] as IssueRec).number) : null,
    },
    totalCount: list.length,
  };
}

function gqlPullsConnection(repo: Repo, args: Record<string, unknown>): GqlObj {
  const all = [...repo.pulls.values()].sort((a, b) => a.number - b.number);
  const first = typeof args.first === 'number' && Number.isFinite(args.first) ? Math.max(0, Math.trunc(args.first)) : 30;
  const slice = all.slice(0, first);
  return {
    __typename: 'PullRequestConnection',
    nodes: slice.map((pull) => gqlPullObj(repo, pull)),
    edges: slice.map((pull) => ({ __typename: 'PullRequestEdge', node: gqlPullObj(repo, pull), cursor: gqlCursorFor(pull.number) })),
    pageInfo: {
      __typename: 'PageInfo',
      hasNextPage: slice.length < all.length,
      hasPreviousPage: false,
      startCursor: null,
      endCursor: null,
    },
    totalCount: all.length,
  };
}

function gqlTypeObj(name: string): GqlObj | null {
  const kind = GQL_TYPE_KINDS[name];
  if (kind === undefined) return null;
  return { __typename: '__Type', name, kind };
}

const GQL_RESOLVERS: Record<string, Record<string, GqlResolver>> = {
  Query: {
    viewer: () => gqlUserObj(viewerLogin ?? ''),
    repository: (_source, args) => {
      const repo = repoForPath(typeof args.owner === 'string' ? args.owner : '', typeof args.name === 'string' ? args.name : '');
      return repo === null ? null : gqlRepoObj(repo);
    },
    node: (_source, args) => {
      const id = typeof args.id === 'string' ? args.id : '';
      const repoHit = repoByGqlId(id);
      if (repoHit !== null) return gqlRepoObj(repoHit);
      const issueHit = issueByGqlId(id);
      if (issueHit !== null) return gqlIssueObj(issueHit.repo, issueHit.issue);
      const pullHit = pullByGqlId(id);
      if (pullHit !== null) return gqlPullObj(pullHit.repo, pullHit.pull);
      const commentHit = commentByGqlId(id);
      if (commentHit !== null) return gqlCommentObj(commentHit.repo, commentHit.issueNumber, commentHit.comment);
      const parsed = parseGqlId(id);
      if (parsed !== null && parsed.type === 'User') return gqlUserObj(viewerLogin ?? '');
      return null;
    },
    nodes: (_source, args, ctx) => {
      const ids = Array.isArray(args.ids) ? args.ids : [];
      const nodeResolver = GQL_RESOLVERS.Query.node as GqlResolver;
      return ids.map((entry) => nodeResolver(_source, { id: entry }, ctx) as GqlObj | null);
    },
    user: (_source, args) => {
      const login = typeof args.login === 'string' ? args.login : '';
      if (viewerLogin !== null && login !== viewerLogin) return null;
      return gqlUserObj(login);
    },
    __type: (_source, args) => gqlTypeObj(typeof args.name === 'string' ? args.name : ''),
    __schema: () => ({ __typename: '__Schema' }),
  },
  Mutation: {
    createIssue: (_source, args) => {
      const input = (typeof args.input === 'object' && args.input !== null ? args.input : {}) as Record<string, unknown>;
      const repo = repoByGqlId(typeof input.repositoryId === 'string' ? input.repositoryId : '');
      if (repo === null) throw new GqlFieldError('Could not resolve the repository for createIssue');
      const result = restCreateIssue(repo, {
        title: typeof input.title === 'string' ? input.title : '',
        body: typeof input.body === 'string' ? input.body : '',
      });
      if (result.status !== 201) throw new GqlFieldError(`createIssue failed: ${(result.body as Record<string, unknown>)?.message ?? result.status}`);
      const number = (result.body as Record<string, unknown>).number as number;
      const issue = repo.issues.get(number) as IssueRec;
      return { __typename: 'CreateIssuePayload', issue: gqlIssueObj(repo, issue), clientMutationId: input.clientMutationId ?? null };
    },
    closeIssue: (_source, args) => {
      const input = (typeof args.input === 'object' && args.input !== null ? args.input : {}) as Record<string, unknown>;
      const hit = issueByGqlId(typeof input.issueId === 'string' ? input.issueId : '');
      if (hit === null) throw new GqlFieldError('Could not resolve the issue for closeIssue');
      const result = restPatchIssue(hit.repo, hit.issue.number, { state: 'closed' });
      if (result.status !== 200) throw new GqlFieldError('closeIssue failed');
      return { __typename: 'CloseIssuePayload', issue: gqlIssueObj(hit.repo, hit.issue), clientMutationId: input.clientMutationId ?? null };
    },
    createPullRequest: (_source, args) => {
      const input = (typeof args.input === 'object' && args.input !== null ? args.input : {}) as Record<string, unknown>;
      const repo = repoByGqlId(typeof input.repositoryId === 'string' ? input.repositoryId : '');
      if (repo === null) throw new GqlFieldError('Could not resolve the repository for createPullRequest');
      const result = restCreatePull(repo, {
        title: typeof input.title === 'string' ? input.title : '',
        body: typeof input.body === 'string' ? input.body : '',
        head: typeof input.headRefName === 'string' ? input.headRefName : '',
        base: typeof input.baseRefName === 'string' ? input.baseRefName : '',
      });
      if (result.status !== 201) throw new GqlFieldError(`createPullRequest failed: ${(result.body as Record<string, unknown>)?.message ?? result.status}`);
      const number = (result.body as Record<string, unknown>).number as number;
      const pull = repo.pulls.get(number) as PullRec;
      return { __typename: 'CreatePullRequestPayload', pullRequest: gqlPullObj(repo, pull), clientMutationId: input.clientMutationId ?? null };
    },
    mergePullRequest: (_source, args) => {
      const input = (typeof args.input === 'object' && args.input !== null ? args.input : {}) as Record<string, unknown>;
      const hit = pullByGqlId(typeof input.pullRequestId === 'string' ? input.pullRequestId : '');
      if (hit === null) throw new GqlFieldError('Could not resolve the pull request for mergePullRequest');
      const method = typeof input.mergeMethod === 'string' ? input.mergeMethod.toLowerCase() : 'merge';
      const result = restMergePull(hit.repo, hit.pull.number, { merge_method: method === 'merge' ? 'merge' : 'squash' });
      if (result.status !== 200) throw new GqlFieldError(`mergePullRequest failed: ${(result.body as Record<string, unknown>)?.message ?? result.status}`);
      return { __typename: 'MergePullRequestPayload', pullRequest: gqlPullObj(hit.repo, hit.pull), clientMutationId: input.clientMutationId ?? null };
    },
    addComment: (_source, args) => {
      const input = (typeof args.input === 'object' && args.input !== null ? args.input : {}) as Record<string, unknown>;
      const hit = issueByGqlId(typeof input.subjectId === 'string' ? input.subjectId : '');
      if (hit === null) throw new GqlFieldError('Could not resolve the subject for addComment');
      const result = restCreateComment(hit.repo, hit.issue.number, { body: typeof input.body === 'string' ? input.body : '' });
      if (result.status !== 201) throw new GqlFieldError('addComment failed');
      const comments = hit.repo.comments.get(hit.issue.number) ?? [];
      const comment = comments[comments.length - 1] as CommentRec;
      return {
        __typename: 'AddCommentPayload',
        commentEdge: { __typename: 'CommentEdge', node: gqlCommentObj(hit.repo, hit.issue.number, comment), cursor: gqlCursorFor(comment.id) },
        subject: gqlIssueObj(hit.repo, hit.issue),
        clientMutationId: input.clientMutationId ?? null,
      };
    },
  },
  User: {
    id: () => gqlId('User', 1000),
    login: (source) => source.login as string,
    name: (source) => source.login as string,
    email: () => '',
    url: () => '',
    avatarUrl: () => '',
    databaseId: () => 1000,
    isViewer: () => true,
    createdAt: () => isoOf(CLOCK_BASE_SEC),
    updatedAt: () => isoOf(CLOCK_BASE_SEC),
  },
  Repository: {
    id: (source) => gqlId('Repository', (source.repo as Repo).id),
    databaseId: (source) => (source.repo as Repo).id,
    name: (source) => (source.repo as Repo).name,
    nameWithOwner: (source) => {
      const repo = source.repo as Repo;
      return `${repo.owner ?? viewerLogin ?? ''}/${repo.name}`;
    },
    description: (source) => (source.repo as Repo).description,
    isPrivate: (source) => (source.repo as Repo).isPrivate,
    isFork: () => false,
    isArchived: () => false,
    isDisabled: () => false,
    isEmpty: (source) => (source.repo as Repo).refs.size === 0,
    owner: (source) => gqlUserObj((source.repo as Repo).owner ?? viewerLogin ?? ''),
    defaultBranchRef: (source) => {
      const repo = source.repo as Repo;
      return repo.refs.has(`refs/heads/${repo.defaultBranch}`) ? { __typename: 'Ref', name: repo.defaultBranch, repo } : null;
    },
    viewerPermission: () => 'ADMIN',
    hasIssuesEnabled: () => true,
    hasProjectsEnabled: () => true,
    hasWikiEnabled: () => true,
    hasDiscussionsEnabled: () => false,
    issue: (source, args) => {
      const repo = source.repo as Repo;
      const issue = repo.issues.get(typeof args.number === 'number' ? args.number : -1);
      return issue === undefined ? null : gqlIssueObj(repo, issue);
    },
    issues: (source, args) => gqlIssuesConnection(source.repo as Repo, args),
    pullRequest: (source, args) => {
      const repo = source.repo as Repo;
      const pull = repo.pulls.get(typeof args.number === 'number' ? args.number : -1);
      return pull === undefined ? null : gqlPullObj(repo, pull);
    },
    pullRequests: (source, args) => gqlPullsConnection(source.repo as Repo, args),
    createdAt: (source) => isoOf((source.repo as Repo).createdSec),
    updatedAt: (source) => isoOf((source.repo as Repo).updatedSec),
    pushedAt: (source) => isoOf((source.repo as Repo).updatedSec),
    url: () => '',
    sshUrl: () => '',
    stargazerCount: () => 0,
    forkCount: () => 0,
  },
  Ref: {
    id: (source) => gqlId('Ref', 0),
    name: (source) => source.name as string,
    prefix: () => 'refs/heads/',
    repository: (source) => (source.repo !== undefined ? gqlRepoObj(source.repo as Repo) : null),
    target: () => null,
  },
  Issue: {
    id: (source) => gqlId('Issue', (source.issue as IssueRec).id),
    databaseId: (source) => (source.issue as IssueRec).id,
    number: (source) => (source.issue as IssueRec).number,
    title: (source) => (source.issue as IssueRec).title,
    state: (source) => (source.issue as IssueRec).state.toUpperCase(),
    body: (source) => (source.issue as IssueRec).body,
    bodyText: (source) => (source.issue as IssueRec).body,
    bodyHTML: (source) => (source.issue as IssueRec).body,
    author: (source) => gqlUserObj(viewerLogin ?? (source.repo as Repo).owner ?? ''),
    repository: (source) => gqlRepoObj(source.repo as Repo),
    labels: (source) => {
      const repo = source.repo as Repo;
      const issue = source.issue as IssueRec;
      const nodes = issue.labels
        .map((name) => repo.labels.get(name))
        .filter((label): label is LabelRec => label !== undefined)
        .map((label) => ({ __typename: 'Label', label }));
      return { __typename: 'LabelConnection', nodes, edges: [], pageInfo: { __typename: 'PageInfo', hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null }, totalCount: nodes.length };
    },
    comments: (source) => {
      const repo = source.repo as Repo;
      const issue = source.issue as IssueRec;
      const nodes = (repo.comments.get(issue.number) ?? []).map((comment) => gqlCommentObj(repo, issue.number, comment));
      return { __typename: 'IssueCommentConnection', nodes, edges: [], pageInfo: { __typename: 'PageInfo', hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null }, totalCount: nodes.length };
    },
    assignees: () => ({ __typename: 'UserConnection', nodes: [], edges: [], pageInfo: { __typename: 'PageInfo', hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null }, totalCount: 0 }),
    milestone: () => null,
    createdAt: (source) => isoOf((source.issue as IssueRec).createdSec),
    updatedAt: (source) => isoOf((source.issue as IssueRec).updatedSec),
    closedAt: (source) => {
      const issue = source.issue as IssueRec;
      return issue.state === 'closed' ? isoOf(issue.updatedSec) : null;
    },
    closed: (source) => (source.issue as IssueRec).state === 'closed',
    url: () => '',
    viewerCanUpdate: () => true,
    viewerCanDelete: () => true,
    viewerDidAuthor: () => true,
    locked: () => false,
    activeLockReason: () => null,
    stateReason: () => null,
  },
  PullRequest: {
    id: (source) => gqlId('PullRequest', (source.pull as PullRec).id),
    databaseId: (source) => (source.pull as PullRec).id,
    number: (source) => (source.pull as PullRec).number,
    title: (source) => (source.pull as PullRec).title,
    state: (source) => {
      const pull = source.pull as PullRec;
      return pull.merged ? 'MERGED' : pull.state.toUpperCase();
    },
    body: (source) => (source.pull as PullRec).body,
    bodyText: (source) => (source.pull as PullRec).body,
    author: (source) => gqlUserObj(viewerLogin ?? (source.repo as Repo).owner ?? ''),
    repository: (source) => gqlRepoObj(source.repo as Repo),
    merged: (source) => (source.pull as PullRec).merged,
    mergedAt: (source) => {
      const pull = source.pull as PullRec;
      return pull.mergedAtSec === null ? null : isoOf(pull.mergedAtSec);
    },
    mergeable: (source) => pullMergeableState(source.repo as Repo, source.pull as PullRec),
    headRefName: (source) => (source.pull as PullRec).headRef,
    baseRefName: (source) => (source.pull as PullRec).baseRef,
    headRef: (source) => {
      const repo = source.repo as Repo;
      const pull = source.pull as PullRec;
      return repo.refs.has(`refs/heads/${pull.headRef}`) ? { __typename: 'Ref', name: pull.headRef, repo } : null;
    },
    baseRef: (source) => {
      const repo = source.repo as Repo;
      const pull = source.pull as PullRec;
      return repo.refs.has(`refs/heads/${pull.baseRef}`) ? { __typename: 'Ref', name: pull.baseRef, repo } : null;
    },
    files: (source, args) => {
      const repo = source.repo as Repo;
      const pull = source.pull as PullRec;
      const all = pullChangedFiles(repo, pull);
      const first = typeof args.first === 'number' && Number.isFinite(args.first) ? Math.max(0, Math.trunc(args.first)) : 30;
      const nodes = all.slice(0, first).map((file) => ({
        __typename: 'PullRequestChangedFile',
        path: file.path,
        additions: file.additions,
        deletions: file.deletions,
        changeType: file.status.toUpperCase(),
      }));
      return { __typename: 'PullRequestChangedFileConnection', nodes, edges: [], pageInfo: { __typename: 'PageInfo', hasNextPage: nodes.length < all.length, hasPreviousPage: false, startCursor: null, endCursor: null }, totalCount: all.length };
    },
    commits: () => ({ __typename: 'PullRequestCommitConnection', nodes: [], edges: [], pageInfo: { __typename: 'PageInfo', hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null }, totalCount: 0 }),
    comments: () => ({ __typename: 'IssueCommentConnection', nodes: [], edges: [], pageInfo: { __typename: 'PageInfo', hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null }, totalCount: 0 }),
    reviews: () => ({ __typename: 'PullRequestReviewConnection', nodes: [], edges: [], pageInfo: { __typename: 'PageInfo', hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null }, totalCount: 0 }),
    labels: () => ({ __typename: 'LabelConnection', nodes: [], edges: [], pageInfo: { __typename: 'PageInfo', hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null }, totalCount: 0 }),
    assignees: () => ({ __typename: 'UserConnection', nodes: [], edges: [], pageInfo: { __typename: 'PageInfo', hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null }, totalCount: 0 }),
    additions: (source) => pullChangedFiles(source.repo as Repo, source.pull as PullRec).reduce((sum, file) => sum + file.additions, 0),
    deletions: (source) => pullChangedFiles(source.repo as Repo, source.pull as PullRec).reduce((sum, file) => sum + file.deletions, 0),
    changedFiles: (source) => pullChangedFiles(source.repo as Repo, source.pull as PullRec).length,
    createdAt: (source) => isoOf((source.pull as PullRec).createdSec),
    updatedAt: (source) => isoOf((source.pull as PullRec).updatedSec),
    closedAt: (source) => {
      const pull = source.pull as PullRec;
      return pull.state === 'closed' ? isoOf(pull.updatedSec) : null;
    },
    closed: (source) => (source.pull as PullRec).state === 'closed',
    url: () => '',
    isDraft: () => false,
    viewerCanUpdate: () => true,
    maintainerCanModify: () => true,
    mergeStateStatus: () => 'CLEAN',
    mergeCommit: () => null,
    potentialMergeCommit: () => null,
  },
  IssueComment: {
    id: (source) => gqlId('IssueComment', (source.comment as CommentRec).id),
    databaseId: (source) => (source.comment as CommentRec).id,
    body: (source) => (source.comment as CommentRec).body,
    bodyText: (source) => (source.comment as CommentRec).body,
    author: (source) => gqlUserObj(viewerLogin ?? (source.repo as Repo).owner ?? ''),
    createdAt: (source) => isoOf((source.comment as CommentRec).createdSec),
    updatedAt: (source) => isoOf((source.comment as CommentRec).updatedSec),
    url: () => '',
    viewerCanUpdate: () => true,
    viewerCanDelete: () => true,
  },
  Label: {
    id: (source) => gqlId('Label', (source.label as LabelRec).id),
    name: (source) => (source.label as LabelRec).name,
    color: (source) => (source.label as LabelRec).color,
    description: (source) => (source.label as LabelRec).description,
    isDefault: () => false,
    url: () => '',
  },
  PageInfo: {
    hasNextPage: (source) => source.hasNextPage as boolean,
    hasPreviousPage: (source) => source.hasPreviousPage as boolean,
    startCursor: (source) => (source.startCursor as string | null) ?? null,
    endCursor: (source) => (source.endCursor as string | null) ?? null,
  },
  IssueConnection: {
    nodes: (source) => source.nodes as GqlObj[],
    edges: (source) => source.edges as GqlObj[],
    pageInfo: (source) => source.pageInfo as GqlObj,
    totalCount: (source) => source.totalCount as number,
  },
  UserConnection: {
    nodes: (source) => (source.nodes as GqlObj[] | undefined) ?? [],
    edges: (source) => (source.edges as GqlObj[] | undefined) ?? [],
    pageInfo: (source) => source.pageInfo as GqlObj,
    totalCount: (source) => (source.totalCount as number | undefined) ?? 0,
  },
  PullRequestCommitConnection: {
    nodes: (source) => (source.nodes as GqlObj[] | undefined) ?? [],
    edges: (source) => (source.edges as GqlObj[] | undefined) ?? [],
    pageInfo: (source) => source.pageInfo as GqlObj,
    totalCount: (source) => (source.totalCount as number | undefined) ?? 0,
  },
  PullRequestReviewConnection: {
    nodes: (source) => (source.nodes as GqlObj[] | undefined) ?? [],
    edges: (source) => (source.edges as GqlObj[] | undefined) ?? [],
    pageInfo: (source) => source.pageInfo as GqlObj,
    totalCount: (source) => (source.totalCount as number | undefined) ?? 0,
  },
  IssueEdge: {
    node: (source) => source.node as GqlObj,
    cursor: (source) => source.cursor as string,
  },
  PullRequestConnection: {
    nodes: (source) => source.nodes as GqlObj[],
    edges: (source) => source.edges as GqlObj[],
    pageInfo: (source) => source.pageInfo as GqlObj,
    totalCount: (source) => source.totalCount as number,
  },
  PullRequestEdge: {
    node: (source) => source.node as GqlObj,
    cursor: (source) => source.cursor as string,
  },
  PullRequestChangedFileConnection: {
    nodes: (source) => source.nodes as GqlObj[],
    edges: (source) => (source.edges as GqlObj[] | undefined) ?? [],
    pageInfo: (source) => source.pageInfo as GqlObj,
    totalCount: (source) => source.totalCount as number,
  },
  PullRequestChangedFile: {
    path: (source) => source.path as string,
    additions: (source) => source.additions as number,
    deletions: (source) => source.deletions as number,
    changeType: (source) => source.changeType as string,
  },
  IssueCommentConnection: {
    nodes: (source) => source.nodes as GqlObj[],
    edges: (source) => (source.edges as GqlObj[] | undefined) ?? [],
    pageInfo: (source) => source.pageInfo as GqlObj,
    totalCount: (source) => source.totalCount as number,
  },
  LabelConnection: {
    nodes: (source) => source.nodes as GqlObj[],
    edges: (source) => (source.edges as GqlObj[] | undefined) ?? [],
    pageInfo: (source) => source.pageInfo as GqlObj,
    totalCount: (source) => source.totalCount as number,
  },
  CommentEdge: {
    node: (source) => source.node as GqlObj,
    cursor: (source) => source.cursor as string,
  },
  CreateIssuePayload: {
    issue: (source) => source.issue as GqlObj,
    clientMutationId: (source) => (source.clientMutationId as string | null) ?? null,
  },
  CloseIssuePayload: {
    issue: (source) => source.issue as GqlObj,
    clientMutationId: (source) => (source.clientMutationId as string | null) ?? null,
  },
  CreatePullRequestPayload: {
    pullRequest: (source) => source.pullRequest as GqlObj,
    clientMutationId: (source) => (source.clientMutationId as string | null) ?? null,
  },
  MergePullRequestPayload: {
    pullRequest: (source) => source.pullRequest as GqlObj,
    clientMutationId: (source) => (source.clientMutationId as string | null) ?? null,
  },
  AddCommentPayload: {
    commentEdge: (source) => source.commentEdge as GqlObj,
    subject: (source) => source.subject as GqlObj,
    clientMutationId: (source) => (source.clientMutationId as string | null) ?? null,
  },
  __Type: {
    name: (source) => source.name as string,
    kind: (source) => source.kind as string,
    description: () => null,
    fields: (source) => {
      const name = source.name as string;
      if (source.kind !== 'OBJECT' && source.kind !== 'INTERFACE') return null;
      return (GQL_TYPE_FIELDS[name] ?? []).map((fieldName) => ({ __typename: '__Field', name: fieldName }));
    },
    enumValues: (source) => {
      const name = source.name as string;
      if (source.kind !== 'ENUM') return null;
      return (GQL_ENUM_VALUES[name] ?? []).map((valueName) => ({ __typename: '__EnumValue', name: valueName }));
    },
    possibleTypes: () => null,
    inputFields: () => null,
    ofType: () => null,
    specifiedByURL: () => null,
    interfaces: () => [],
  },
  __Field: {
    name: (source) => source.name as string,
    description: () => null,
    args: () => [],
    type: () => null,
    isDeprecated: () => false,
    deprecationReason: () => null,
  },
  __EnumValue: {
    name: (source) => source.name as string,
    description: () => null,
    isDeprecated: () => false,
    deprecationReason: () => null,
  },
  __Schema: {
    queryType: () => gqlTypeObj('Query'),
    mutationType: () => gqlTypeObj('Mutation'),
    subscriptionType: () => null,
    types: () => Object.keys(GQL_TYPE_KINDS).sort().map((name) => gqlTypeObj(name)),
    directives: () => [],
    description: () => null,
  },
};

function gqlResolveValue(value: GqlValue, ctx: GqlExecCtx): unknown {
  switch (value.kind) {
    case 'variable':
      return ctx.variables[value.name];
    case 'string':
    case 'int':
    case 'float':
    case 'boolean':
    case 'enum':
      return value.value;
    case 'null':
      return null;
    case 'list':
      return value.values.map((entry) => gqlResolveValue(entry, ctx));
    case 'object': {
      const out: Record<string, unknown> = {};
      for (const field of value.fields) out[field.name] = gqlResolveValue(field.value, ctx);
      return out;
    }
  }
}

function gqlCompleteValue(value: unknown, selectionSet: GqlSelection[] | null, ctx: GqlExecCtx, path: (string | number)[]): unknown {
  if (value === null || value === undefined) return null;
  if (Array.isArray(value)) return value.map((entry, index) => gqlCompleteValue(entry, selectionSet, ctx, [...path, index]));
  if (typeof value === 'object' && typeof (value as GqlObj).__typename === 'string') {
    const obj = value as GqlObj;
    return gqlExecuteSelectionSet(obj.__typename, obj, selectionSet ?? [], ctx, path);
  }
  return value;
}

function gqlExecuteSelectionSet(
  typeName: string,
  source: GqlObj,
  selections: GqlSelection[],
  ctx: GqlExecCtx,
  path: (string | number)[],
): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  const applySelections = (currentType: string, currentSource: GqlObj, currentSelections: GqlSelection[]): void => {
    for (const selection of currentSelections) {
      if (selection.kind === 'inline') {
        if (selection.typeCondition === null || selection.typeCondition === currentType) {
          applySelections(currentType, currentSource, selection.selectionSet);
        }
        continue;
      }
      if (selection.kind === 'spread') {
        const fragment = ctx.fragments.get(selection.name);
        if (fragment !== undefined && (fragment.typeCondition === null || fragment.typeCondition === currentType)) {
          applySelections(currentType, currentSource, fragment.selectionSet);
        }
        continue;
      }
      const key = selection.alias ?? selection.name;
      if (selection.name === '__typename') {
        out[key] = currentType;
        continue;
      }
      const resolver = GQL_RESOLVERS[currentType]?.[selection.name];
      if (resolver === undefined) {
        ctx.errors.push({ message: `Field '${selection.name}' doesn't exist on type '${currentType}'`, path: [...path, key] });
        out[key] = null;
        continue;
      }
      const args: Record<string, unknown> = {};
      for (const arg of selection.args) args[arg.name] = gqlResolveValue(arg.value, ctx);
      let raw: unknown;
      try {
        raw = resolver(currentSource, args, ctx);
      } catch (err) {
        ctx.errors.push({ message: err instanceof Error ? err.message : String(err), path: [...path, key] });
        out[key] = null;
        continue;
      }
      out[key] = gqlCompleteValue(raw, selection.selectionSet, ctx, [...path, key]);
    }
  };
  applySelections(typeName, source, selections);
  return out;
}

/** Execute one operation document (a single entry of a possibly batched request). */
function executeGraphqlOperation(body: Record<string, unknown>): Record<string, unknown> {
  if (typeof body.query !== 'string' || body.query === '') {
    return { errors: [{ message: 'Must provide query string.' }] };
  }
  let document: GqlDocument;
  try {
    document = new GqlParser(body.query).parseDocument();
  } catch (err) {
    return { errors: [{ message: err instanceof Error ? err.message : String(err) }] };
  }
  const variables = (typeof body.variables === 'object' && body.variables !== null ? body.variables : {}) as Record<string, unknown>;
  let operation: GqlOperation | undefined;
  if (typeof body.operationName === 'string') operation = document.operations.find((entry) => entry.name === body.operationName);
  operation ??= document.operations[0];
  if (operation === undefined) return { errors: [{ message: 'No operation found in the document.' }] };
  const ctx: GqlExecCtx = { variables, fragments: document.fragments, errors: [] };
  const rootType = operation.operation === 'mutation' ? 'Mutation' : 'Query';
  const data = gqlExecuteSelectionSet(rootType, { __typename: rootType }, operation.selectionSet, ctx, []);
  const out: Record<string, unknown> = { data };
  if (ctx.errors.length > 0) out.errors = ctx.errors;
  return out;
}

async function handleGraphqlRoute(req: IncomingMessage, res: ServerResponse): Promise<void> {
  if (req.method !== 'POST') {
    sendJson(res, 405, { message: 'Method Not Allowed' });
    return;
  }
  if (!authorized(req)) {
    sendJson(res, 401, { message: 'Bad credentials' });
    return;
  }
  const raw = await readBody(req);
  let parsed: unknown;
  try {
    parsed = JSON.parse(raw.toString('utf8'));
  } catch {
    sendJson(res, 400, { errors: [{ message: 'Problems parsing JSON' }] });
    return;
  }
  if (Array.isArray(parsed)) {
    const responses = parsed.map((entry) =>
      typeof entry === 'object' && entry !== null ? executeGraphqlOperation(entry as Record<string, unknown>) : { errors: [{ message: 'Invalid operation entry.' }] },
    );
    sendJson(res, 200, responses);
    return;
  }
  if (typeof parsed !== 'object' || parsed === null) {
    sendJson(res, 400, { errors: [{ message: 'Invalid request body.' }] });
    return;
  }
  sendJson(res, 200, executeGraphqlOperation(parsed as Record<string, unknown>));
}

// --------------------------------------------------------------------------- MCP (agent-native surface)
//
// The Model Context Protocol endpoint at /mcp, Streamable HTTP. Speaks the modern 2026-07-28
// era (server/discover, no session) and answers the legacy initialize handshake too. Tools act
// on the same store as REST and GraphQL — every tool is a thin call into the REST handlers.

const MCP_SERVER_INFO = { name: 'makefun-forge', version: FORGE_VERSION };
const MCP_SUPPORTED_VERSIONS = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];

const MCP_TOOLS: readonly Record<string, unknown>[] = Object.freeze([
  {
    name: 'create_repo',
    description: 'Create a new repository owned by the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'The name of the repository to create.' },
        description: { type: 'string', description: 'A short description of the repository.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by its owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The issue title.' },
        body: { type: 'string', description: 'The issue body.' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'list_issues',
    description: 'List the issues of a repository, optionally filtered by state.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        state: { type: 'string', description: 'Filter by state: open, closed or all.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request from a head branch into a base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The pull request title.' },
        body: { type: 'string', description: 'The pull request body.' },
        head: { type: 'string', description: 'The head branch to merge from.' },
        base: { type: 'string', description: 'The base branch to merge into.' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request by number.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        pull_number: { type: 'number', description: 'The pull request number to merge.' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
]);

const MCP_TOOL_NAMES = new Set(MCP_TOOLS.map((tool) => tool.name as string));

function mcpToolSuccess(value: unknown): Record<string, unknown> {
  return { content: [{ type: 'text', text: JSON.stringify(value) }], structuredContent: value, isError: false };
}

function mcpToolFailure(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], isError: true };
}

/** Run one tool against the store; tool-level problems are isError results, never throws. */
function mcpCallTool(name: string, args: Record<string, unknown>): Record<string, unknown> {
  const str = (value: unknown): string => (typeof value === 'string' ? value : '');
  const repoArg = (): Repo | null => {
    const owner = str(args.owner);
    const repoName = str(args.repo);
    if (owner === '' || repoName === '') return null;
    return repoForPath(owner, repoName);
  };
  switch (name) {
    case 'create_repo': {
      const repoName = str(args.name);
      if (repoName === '') return mcpToolFailure('create_repo requires a "name" argument');
      const result = restCreateRepo({
        name: repoName,
        description: typeof args.description === 'string' ? args.description : undefined,
        private: typeof args.private === 'boolean' ? args.private : undefined,
      });
      if (result.status !== 201) return mcpToolFailure(`create_repo failed: ${(result.body as Record<string, unknown>)?.message ?? `HTTP ${result.status}`}`);
      return mcpToolSuccess(result.body);
    }
    case 'get_repo': {
      const repo = repoArg();
      if (repo === null) return mcpToolFailure(`repository ${str(args.owner)}/${str(args.repo)} was not found`);
      return mcpToolSuccess(repoJson(repo));
    }
    case 'create_issue': {
      const repo = repoArg();
      if (repo === null) return mcpToolFailure(`repository ${str(args.owner)}/${str(args.repo)} was not found`);
      const title = str(args.title);
      if (title === '') return mcpToolFailure('create_issue requires a "title" argument');
      const result = restCreateIssue(repo, { title, body: str(args.body) });
      if (result.status !== 201) return mcpToolFailure(`create_issue failed: ${(result.body as Record<string, unknown>)?.message ?? `HTTP ${result.status}`}`);
      return mcpToolSuccess(result.body);
    }
    case 'list_issues': {
      const repo = repoArg();
      if (repo === null) return mcpToolFailure(`repository ${str(args.owner)}/${str(args.repo)} was not found`);
      const state = str(args.state);
      let issues = [...repo.issues.values()];
      if (state === 'open' || state === 'closed') issues = issues.filter((issue) => issue.state === state);
      issues.sort((a, b) => a.number - b.number);
      return mcpToolSuccess(issues.map((issue) => issueJson(repo, issue)));
    }
    case 'create_pull_request': {
      const repo = repoArg();
      if (repo === null) return mcpToolFailure(`repository ${str(args.owner)}/${str(args.repo)} was not found`);
      const result = restCreatePull(repo, { title: str(args.title), body: str(args.body), head: str(args.head), base: str(args.base) });
      if (result.status !== 201) return mcpToolFailure(`create_pull_request failed: ${(result.body as Record<string, unknown>)?.message ?? `HTTP ${result.status}`}`);
      return mcpToolSuccess(result.body);
    }
    case 'merge_pull_request': {
      const repo = repoArg();
      if (repo === null) return mcpToolFailure(`repository ${str(args.owner)}/${str(args.repo)} was not found`);
      const number = typeof args.pull_number === 'number' ? args.pull_number : Number(args.pull_number);
      if (!Number.isInteger(number) || number < 1) return mcpToolFailure('merge_pull_request requires a "pull_number" argument');
      const result = restMergePull(repo, number, {});
      if (result.status !== 200) return mcpToolFailure(`merge_pull_request failed: ${(result.body as Record<string, unknown>)?.message ?? `HTTP ${result.status}`}`);
      const pull = repo.pulls.get(number) as PullRec;
      return mcpToolSuccess(pullJson(repo, pull));
    }
    default:
      return mcpToolFailure(`unknown tool: ${name}`);
  }
}

/** Dispatch one JSON-RPC message; returns the response object, or null for a notification. */
function mcpDispatch(message: Record<string, unknown>): Record<string, unknown> | null {
  const method = typeof message.method === 'string' ? message.method : '';
  const hasId = 'id' in message;
  const id = hasId ? message.id : null;
  const params = (typeof message.params === 'object' && message.params !== null ? message.params : {}) as Record<string, unknown>;
  const respond = (result: unknown): Record<string, unknown> => ({ jsonrpc: '2.0', id, result });
  const respondError = (code: number, text: string): Record<string, unknown> => ({ jsonrpc: '2.0', id, error: { code, message: text } });
  switch (method) {
    case 'server/discover':
      return respond({
        resultType: 'complete',
        supportedVersions: MCP_SUPPORTED_VERSIONS,
        capabilities: { tools: {} },
        serverInfo: MCP_SERVER_INFO,
        _meta: { 'io.modelcontextprotocol/serverInfo': MCP_SERVER_INFO },
      });
    case 'initialize':
      return respond({
        protocolVersion:
          typeof params.protocolVersion === 'string' && MCP_SUPPORTED_VERSIONS.includes(params.protocolVersion) ? params.protocolVersion : '2025-11-25',
        capabilities: { tools: {} },
        serverInfo: MCP_SERVER_INFO,
      });
    case 'ping':
      return respond({});
    case 'tools/list':
      return respond({ tools: MCP_TOOLS });
    case 'tools/call': {
      const name = typeof params.name === 'string' ? params.name : '';
      if (!MCP_TOOL_NAMES.has(name)) return respondError(-32602, `Unknown tool: ${name}`);
      const toolArgs = (typeof params.arguments === 'object' && params.arguments !== null ? params.arguments : {}) as Record<string, unknown>;
      try {
        return respond(mcpCallTool(name, toolArgs));
      } catch (err) {
        return respond(mcpToolFailure(err instanceof Error ? err.message : String(err)));
      }
    }
    default:
      if (!hasId || method.startsWith('notifications/')) return null;
      return respondError(-32601, `Method not found: ${method}`);
  }
}

async function handleMcpRoute(req: IncomingMessage, res: ServerResponse): Promise<void> {
  if (req.method === 'DELETE') {
    // A legacy session close; the forge keeps no sessions, so this is a polite no-op.
    res.writeHead(200, { 'x-github-request-id': nextRequestId() });
    res.end();
    return;
  }
  if (req.method !== 'POST') {
    sendJson(res, 405, { message: 'Method Not Allowed' });
    return;
  }
  const raw = (await readBody(req)).toString('utf8');
  let parsed: unknown;
  try {
    parsed = JSON.parse(raw);
  } catch {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  if (!authorized(req)) {
    sendJson(res, 401, { message: 'Bad credentials' });
    return;
  }
  if (Array.isArray(parsed)) {
    const responses: Record<string, unknown>[] = [];
    for (const entry of parsed) {
      if (typeof entry === 'object' && entry !== null) {
        const response = mcpDispatch(entry as Record<string, unknown>);
        if (response !== null) responses.push(response);
      }
    }
    sendJson(res, 200, responses);
    return;
  }
  if (typeof parsed !== 'object' || parsed === null) {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32600, message: 'Invalid Request' } });
    return;
  }
  const response = mcpDispatch(parsed as Record<string, unknown>);
  if (response === null) {
    res.writeHead(202, { 'x-github-request-id': nextRequestId() });
    res.end();
    return;
  }
  sendJson(res, 200, response);
}

// --------------------------------------------------------------------------- HTTP plumbing

const EXPECTED_TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
let requestCounter = 0;

function nextRequestId(): string {
  requestCounter += 1;
  return `req-${requestCounter}`;
}

function authorized(req: IncomingMessage): boolean {
  const header = req.headers.authorization;
  if (typeof header !== 'string') return false;
  const match = /^Bearer (.+)$/.exec(header);
  if (!match) return false;
  if (EXPECTED_TOKEN === '') return true; // local dev without a configured token: any bearer token names the viewer
  return match[1] === EXPECTED_TOKEN;
}

function sendJson(res: ServerResponse, status: number, body: unknown, headers: Record<string, string> = {}): void {
  const payload = body === undefined ? '' : JSON.stringify(body);
  res.writeHead(status, {
    'content-type': 'application/json; charset=utf-8',
    'x-github-request-id': nextRequestId(),
    // An explicit length keeps responses off chunked framing: one write, no chunk markers.
    ...(payload !== '' ? { 'content-length': Buffer.byteLength(payload) } : {}),
    ...headers,
  });
  res.end(payload);
}

function sendBuffer(res: ServerResponse, status: number, body: Buffer, contentType: string): void {
  res.writeHead(status, {
    'content-type': contentType,
    'x-github-request-id': nextRequestId(),
    'content-length': body.length,
  });
  res.end(body);
}

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on('data', (chunk: Buffer) => chunks.push(chunk));
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

/** Parse a JSON request body: an empty body is {}, malformed JSON is a 400. */
function parseJsonBody(raw: Buffer): { ok: true; body: Record<string, unknown> } | { ok: false; result: ApiResult } {
  if (raw.length === 0) return { ok: true, body: {} };
  try {
    const parsed: unknown = JSON.parse(raw.toString('utf8'));
    if (typeof parsed !== 'object' || parsed === null || Array.isArray(parsed)) return { ok: true, body: {} };
    return { ok: true, body: parsed as Record<string, unknown> };
  } catch {
    return { ok: false, result: apiError(400, 'Problems parsing JSON') };
  }
}

// --------------------------------------------------------------------------- git response cache

/**
 * Memoized smart-HTTP responses. An info/refs advertisement or an upload-pack answer is a
 * pure function of the repository's git state — its refs, its default branch, and its object
 * set (objects are immutable and never deleted, so the set is pinned by refs plus count) —
 * and of the request itself. Identical requests against unchanged state can therefore be
 * answered with the very bytes the first computation produced; the clone workload (fifty
 * identical depth-1 fetches) is exactly that pattern. The state fingerprint is part of every
 * key, so any push or ref update changes the key and stale entries simply age out. The cache
 * is bounded in entries and bytes, and lookups happen only after auth and repo resolution.
 */
interface GitCacheEntry {
  body: Buffer;
  contentType: string;
}

const gitResponseCache = new Map<string, GitCacheEntry>();
let gitResponseCacheBytes = 0;
const GIT_CACHE_MAX_ENTRIES = 256;
const GIT_CACHE_MAX_BYTES = 32 * 1024 * 1024;
const GIT_CACHE_MAX_ENTRY_BYTES = 8 * 1024 * 1024;

function repoGitFingerprint(repo: Repo): string {
  let fingerprint = `${repo.objects.size}|${repo.defaultBranch}|`;
  for (const ref of sortedRefs(repo)) fingerprint += `${ref.name}=${ref.oid};`;
  return fingerprint;
}

function gitCacheGet(key: string): GitCacheEntry | undefined {
  const entry = gitResponseCache.get(key);
  if (entry !== undefined) {
    // Refresh recency so hot entries survive eviction.
    gitResponseCache.delete(key);
    gitResponseCache.set(key, entry);
  }
  return entry;
}

function gitCachePut(key: string, entry: GitCacheEntry): void {
  if (entry.body.length > GIT_CACHE_MAX_ENTRY_BYTES) return;
  const existing = gitResponseCache.get(key);
  if (existing !== undefined) {
    gitResponseCacheBytes -= existing.body.length;
    gitResponseCache.delete(key);
  }
  gitResponseCache.set(key, entry);
  gitResponseCacheBytes += entry.body.length;
  while (gitResponseCache.size > GIT_CACHE_MAX_ENTRIES || gitResponseCacheBytes > GIT_CACHE_MAX_BYTES) {
    const oldest = gitResponseCache.keys().next();
    if (oldest.done) break;
    const evicted = gitResponseCache.get(oldest.value);
    gitResponseCache.delete(oldest.value);
    if (evicted !== undefined) gitResponseCacheBytes -= evicted.body.length;
  }
}

// --------------------------------------------------------------------------- routing

async function handleGitRoute(req: IncomingMessage, res: ServerResponse, owner: string, repoName: string, tail: string): Promise<void> {
  if (!authorized(req)) {
    sendJson(res, 401, { message: 'Bad credentials' });
    return;
  }
  const repo = repoForPath(owner, repoName);
  if (!repo) {
    sendJson(res, 404, { message: 'Not Found' });
    return;
  }
  const url = new URL(req.url ?? '/', 'http://forge.invalid');
  if (tail === 'info/refs' && req.method === 'GET') {
    const service = url.searchParams.get('service');
    if (service !== 'git-upload-pack' && service !== 'git-receive-pack') {
      sendJson(res, 400, { message: 'Unsupported service' });
      return;
    }
    const protocolHeader = req.headers['git-protocol'] as string | undefined ?? null;
    const cacheKey = `refs|${owner}|${repoName}|${service}|${protocolHeader ?? ''}|${repoGitFingerprint(repo)}`;
    const hit = gitCacheGet(cacheKey);
    if (hit !== undefined) {
      sendBuffer(res, 200, hit.body, hit.contentType);
      return;
    }
    const result = handleInfoRefs(repo, service, protocolHeader);
    gitCachePut(cacheKey, result);
    sendBuffer(res, 200, result.body, result.contentType);
    return;
  }
  if (tail === 'git-upload-pack' && req.method === 'POST') {
    const raw = await readBody(req);
    const cacheKey = `up|${owner}|${repoName}|${repoGitFingerprint(repo)}|${sha1Hex(raw)}`;
    const hit = gitCacheGet(cacheKey);
    if (hit !== undefined) {
      sendBuffer(res, 200, hit.body, hit.contentType);
      return;
    }
    try {
      const body = handleUploadPack(repo, raw);
      gitCachePut(cacheKey, { body, contentType: 'application/x-git-upload-pack-result' });
      sendBuffer(res, 200, body, 'application/x-git-upload-pack-result');
    } catch {
      sendBuffer(res, 400, Buffer.from('ERR unsupported request\n', 'utf8'), 'application/x-git-upload-pack-result');
    }
    return;
  }
  if (tail === 'git-receive-pack' && req.method === 'POST') {
    const raw = await readBody(req);
    try {
      const body = await handleReceivePack(repo, raw);
      sendBuffer(res, 200, body, 'application/x-git-receive-pack-result');
    } catch {
      sendBuffer(res, 400, Buffer.from('ERR unsupported request\n', 'utf8'), 'application/x-git-receive-pack-result');
    }
    return;
  }
  sendJson(res, 404, { message: 'Not Found' });
}

async function handleApiRoute(req: IncomingMessage, res: ServerResponse, segments: string[], query: URLSearchParams, host: string, rawPath: string): Promise<void> {
  const method = req.method ?? 'GET';
  const send = (result: ApiResult): void => {
    if (result.status === 204) {
      res.writeHead(204, { 'x-github-request-id': nextRequestId() });
      res.end();
      return;
    }
    sendJson(res, result.status, result.body, result.headers ?? {});
  };
  const body = async (): Promise<Record<string, unknown> | null> => {
    const parsed = parseJsonBody(await readBody(req));
    if (!parsed.ok) {
      send(parsed.result);
      return null;
    }
    return parsed.body;
  };

  // segments[0] === 'api', segments[1] === 'v3'
  const rest = segments.slice(2);

  if (rest.length === 0) {
    if (method !== 'GET') return send(apiError(404, 'Not Found'));
    if (!authorized(req)) return send(apiError(401, 'Bad credentials'));
    return send({
      status: 200,
      headers: { 'x-oauth-scopes': 'repo, user', 'x-accepted-oauth-scopes': 'repo, user' },
      body: {
        current_user_url: '/api/v3/user',
        current_user_repositories_url: '/api/v3/user/repos',
        repository_url: '/api/v3/repos/{owner}/{repo}',
        installed_version: FORGE_VERSION,
      },
    });
  }

  if (rest[0] === 'meta' && rest.length === 1) {
    if (!authorized(req)) return send(apiError(401, 'Bad credentials'));
    return send({ status: 200, body: { installed_version: FORGE_VERSION, github_developer_version: FORGE_VERSION } });
  }

  if (rest[0] === 'user' && rest.length === 1 && method === 'GET') {
    if (!authorized(req)) return send(apiError(401, 'Bad credentials'));
    return send({ status: 200, body: userJson(viewerLogin ?? '') });
  }

  if (rest[0] === 'user' && rest[1] === 'repos' && rest.length === 2) {
    if (!authorized(req)) return send(apiError(401, 'Bad credentials'));
    if (method === 'GET') return send(restListUserRepos(query, host, rawPath));
    if (method === 'POST') {
      const parsed = await body();
      if (parsed === null) return;
      return send(restCreateRepo(parsed));
    }
    return send(apiError(404, 'Not Found'));
  }

  if (rest[0] === 'repos' && rest.length >= 3) {
    const owner = rest[1] as string;
    const name = rest[2] as string;
    const tail = rest.slice(3);
    if (!authorized(req)) return send(apiError(401, 'Bad credentials'));
    learnViewer(owner);
    const repo = repoForPath(owner, name);
    if (!repo) return send(apiError(404, 'Not Found'));

    if (tail.length === 0) {
      if (method === 'GET') return send(restGetRepo(repo));
      if (method === 'PATCH') {
        const parsed = await body();
        if (parsed === null) return;
        return send(restPatchRepo(repo, parsed));
      }
      if (method === 'DELETE') return send(restDeleteRepo(repo));
      return send(apiError(404, 'Not Found'));
    }
    if (tail[0] === 'branches' && tail.length === 1 && method === 'GET') return send(restListBranches(repo));
    if (tail[0] === 'commits' && tail.length === 1 && method === 'GET') return send(restListCommits(repo, query));
    if (tail[0] === 'git' && tail[1] === 'refs' && tail.length === 2 && method === 'POST') {
      const parsed = await body();
      if (parsed === null) return;
      return send(restCreateRef(repo, parsed));
    }
    if (tail[0] === 'contents') {
      const contentPath = tail.slice(1).join('/');
      if (method === 'GET') return send(restGetContents(repo, contentPath, query));
      if (method === 'PUT') {
        const parsed = await body();
        if (parsed === null) return;
        return send(restPutContents(repo, contentPath, parsed));
      }
      if (method === 'DELETE') {
        const parsed = await body();
        if (parsed === null) return;
        return send(restDeleteContents(repo, contentPath, parsed));
      }
      return send(apiError(404, 'Not Found'));
    }
    if (tail[0] === 'labels' && tail.length === 1) {
      if (method === 'POST') {
        const parsed = await body();
        if (parsed === null) return;
        return send(restCreateLabel(repo, parsed));
      }
      if (method === 'GET') return send({ status: 200, body: [...repo.labels.values()].map(labelJson) });
      return send(apiError(404, 'Not Found'));
    }
    if (tail[0] === 'issues' && tail.length === 1) {
      if (method === 'GET') return send(restListIssues(repo, query, host, rawPath));
      if (method === 'POST') {
        const parsed = await body();
        if (parsed === null) return;
        return send(restCreateIssue(repo, parsed));
      }
      return send(apiError(404, 'Not Found'));
    }
    if (tail[0] === 'issues' && tail.length >= 2) {
      const number = Number(tail[1]);
      if (!Number.isInteger(number) || number < 1) return send(apiError(404, 'Not Found'));
      if (tail.length === 2) {
        if (method === 'GET') return send(restGetIssue(repo, number));
        if (method === 'PATCH') {
          const parsed = await body();
          if (parsed === null) return;
          return send(restPatchIssue(repo, number, parsed));
        }
        return send(apiError(404, 'Not Found'));
      }
      if (tail.length === 3 && tail[2] === 'comments') {
        if (method === 'GET') return send(restListComments(repo, number));
        if (method === 'POST') {
          const parsed = await body();
          if (parsed === null) return;
          return send(restCreateComment(repo, number, parsed));
        }
        return send(apiError(404, 'Not Found'));
      }
      return send(apiError(404, 'Not Found'));
    }
    if (tail[0] === 'pulls' && tail.length === 1) {
      if (method === 'GET') return send(restListPulls(repo, query, host, rawPath));
      if (method === 'POST') {
        const parsed = await body();
        if (parsed === null) return;
        return send(restCreatePull(repo, parsed));
      }
      return send(apiError(404, 'Not Found'));
    }
    if (tail[0] === 'pulls' && tail.length >= 2) {
      const number = Number(tail[1]);
      if (!Number.isInteger(number) || number < 1) return send(apiError(404, 'Not Found'));
      if (tail.length === 2 && method === 'GET') return send(restGetPull(repo, number));
      if (tail.length === 3 && tail[2] === 'files' && method === 'GET') return send(restPullFiles(repo, number));
      if (tail.length === 3 && tail[2] === 'merge' && method === 'PUT') {
        const parsed = await body();
        if (parsed === null) return;
        return send(restMergePull(repo, number, parsed));
      }
      return send(apiError(404, 'Not Found'));
    }
    return send(apiError(404, 'Not Found'));
  }

  return send(apiError(404, 'Not Found'));
}

async function handleRequest(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const url = new URL(req.url ?? '/', 'http://forge.invalid');
  const rawPath = url.pathname;
  const segments = rawPath
    .split('/')
    .filter((segment) => segment !== '')
    .map((segment) => {
      try {
        return decodeURIComponent(segment);
      } catch {
        return segment;
      }
    });
  const host = (req.headers.host as string | undefined) ?? '127.0.0.1';

  if (rawPath === '/healthz') {
    sendJson(res, 200, { ok: true });
    return;
  }

  // Git smart HTTP: /{owner}/{repo}.git/{info/refs|git-upload-pack|git-receive-pack}
  if (segments.length === 3 && (segments[1] as string).endsWith('.git')) {
    const owner = segments[0] as string;
    const repoName = (segments[1] as string).slice(0, -'.git'.length);
    const tail = segments[2] as string;
    if (tail === 'info/refs' || tail === 'git-upload-pack' || tail === 'git-receive-pack') {
      await handleGitRoute(req, res, owner, repoName, tail);
      return;
    }
  }
  if (segments.length === 4 && (segments[1] as string).endsWith('.git') && segments[2] === 'info' && segments[3] === 'refs') {
    await handleGitRoute(req, res, segments[0] as string, (segments[1] as string).slice(0, -'.git'.length), 'info/refs');
    return;
  }

  if (segments[0] === 'api' && segments[1] === 'v3') {
    await handleApiRoute(req, res, segments, url.searchParams, host, rawPath);
    return;
  }

  if (segments[0] === 'api' && segments[1] === 'graphql' && segments.length === 2) {
    await handleGraphqlRoute(req, res);
    return;
  }

  if (segments.length === 1 && segments[0] === 'mcp') {
    await handleMcpRoute(req, res);
    return;
  }

  sendJson(res, 404, { message: 'Not Found' });
}

// --------------------------------------------------------------------------- lifecycle

const server = createServer((req, res) => {
  handleRequest(req, res).catch(() => {
    if (!res.headersSent) sendJson(res, 500, { message: 'Internal Server Error' });
    else res.end();
  });
});
server.keepAliveTimeout = 65_000;
server.headersTimeout = 70_000;

/** One small HTTP call against the env harness (register / done polling), stdlib only. */
function harnessCall(method: 'GET' | 'POST', target: string, payload?: string): Promise<{ status: number; text: string }> {
  return new Promise((resolve, reject) => {
    const url = new URL(target);
    const request = (url.protocol === 'https:' ? httpsRequest : httpRequest)(
      {
        hostname: url.hostname,
        port: url.port === '' ? (url.protocol === 'https:' ? 443 : 80) : Number(url.port),
        path: `${url.pathname}${url.search}`,
        method,
        headers: payload === undefined ? {} : { 'content-type': 'application/json', 'content-length': Buffer.byteLength(payload) },
      },
      (response: IncomingMessage) => {
        const chunks: Buffer[] = [];
        response.on('data', (chunk: Buffer) => chunks.push(chunk));
        response.on('end', () => resolve({ status: response.statusCode ?? 0, text: Buffer.concat(chunks).toString('utf8') }));
      },
    );
    request.on('error', reject);
    if (payload !== undefined) request.write(payload);
    request.end();
  });
}

async function runWithHarness(envUrl: string): Promise<void> {
  await new Promise<void>((resolve) => {
    server.listen(0, () => resolve());
  });
  const address = server.address();
  const port = typeof address === 'object' && address !== null ? address.port : 0;
  const base = envUrl.replace(/\/+$/, '');
  let registered = false;
  for (let attempt = 0; attempt < 50 && !registered; attempt += 1) {
    try {
      const response = await harnessCall('POST', `${base}/register`, JSON.stringify({ port }));
      registered = response.status >= 200 && response.status < 300;
    } catch {
      registered = false;
    }
    if (!registered) await new Promise((resolve) => setTimeout(resolve, 200));
  }
  for (;;) {
    try {
      const response = await harnessCall('GET', `${base}/done`);
      const parsed: unknown = JSON.parse(response.text);
      if (typeof parsed === 'object' && parsed !== null && (parsed as Record<string, unknown>).done === true) break;
    } catch {
      // The harness is not answering yet; keep serving and poll again.
    }
    await new Promise((resolve) => setTimeout(resolve, 200));
  }
  server.close(() => process.exit(0));
  setTimeout(() => process.exit(0), 2_000).unref();
}

// A single bad request must never take the forge down; log and keep serving.
process.on('uncaughtException', (err) => {
  process.stderr.write(`uncaught: ${err instanceof Error ? err.stack ?? err.message : String(err)}\n`);
});
process.on('unhandledRejection', (err) => {
  process.stderr.write(`unhandled rejection: ${err instanceof Error ? err.stack ?? err.message : String(err)}\n`);
});

const envUrl = process.env.MAKEFUN_ENV_URL;
if (envUrl !== undefined && envUrl !== '') {
  runWithHarness(envUrl).catch(() => process.exit(1));
} else {
  const port = Number(process.env.PORT ?? '8077');
  server.listen(port, () => {
    process.stderr.write(`forge listening on ${port}\n`);
  });
}
