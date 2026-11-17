# Forge notes — rounds 1–2 (17 Nov 2026)

Single-file implementation in `main.ts` (Node stdlib only, type-strippable TS, in-memory store).

## Verified locally (fresh process, kit runner `sdk/run.ts --perf`)

| group    | result |
| -------- | ------ |
| git      | 30/30  |
| repos    | 15/15  |
| issues   | 15/15  |
| pulls    | 20/20  |
| protocol | 5/5    |
| graphql  | 20/20  |
| mcp      | 15/15  |

**120/120 — feature column 600/600, agent column 200/200, total 975–984/1000 on this machine**
(the perf column moved 175↔184 between runs on box noise alone).

Perf medians across the two full runs (calibration references in parentheses):
push 683–717 ms (~1641), clone 89–107 ms (~267), read 576–830 ms (~2760), write 99–110 ms (~349).

**Determinism / replay evidence**: the suite was run twice against two fresh forge processes;
all 120 per-check verdicts *and* detail strings are byte-identical between the runs (the details
embed commit shas, object counts and ids, so identical details mean identical observable state
sequences). No `Date.now()`/`Math.random()` anywhere: sequential counters + the logical clock.

Harness lifecycle also verified against a fake env: with `MAKEFUN_ENV_URL` set the forge
binds an ephemeral port, POSTs `{"port": n}` to `/register`, serves, polls `/done`, exits 0.

## Design decisions worth knowing

- **Viewer identity**: the bearer token names one viewer; repositories are keyed by name and
  bound to the first owner login that addresses them. The same name under another login is
  404, never 403 (repos.foreign-token). `viewerLogin` is learned from owner-bearing paths.
- **Determinism**: sequential ids/counters everywhere; timestamps come from a logical clock
  (2026-01-01T00:00:00Z + tick), never `Date.now()`/`Math.random()`.
- **Pack reading**: Node 24's zlib streams expose no consumed-byte count, so the deflate
  stream end is found by binary search — `inflateSync` ignores trailing bytes and throws on
  truncated input, making the smallest successful prefix the exact end. Delta resolution
  (ofs/ref) is implemented; packs are written without deltas (allowed by the checks).
- **Fetch**: have-closure is cut at the client's shallow commits; shallow/unshallow lines are
  computed from parent availability after the send set is known. Depth is absolute from the
  wants (deepen N ⇒ generations 0..N-1), which is what fetch-shallow-deepen expects.
- **Push**: report-status is wrapped in side-band-64k band-1 packets when the client requests
  that capability; non-fast-forward ref updates are refused per-ref with the exact reason
  `non-fast-forward`, and only `ok` refs are applied.
- **Issues/PRs share one per-repo number sequence**, as on GitHub. PR merge does a per-path
  three-way merge against the merge-base; both-sides-changed paths ⇒ 405. Squash merges get a
  single parent; `merge_method: "merge"` gets two.
- **Labels are not pre-seeded**: checks create the label they use and expect 201, so a fresh
  repo starts with no labels; unknown labels on issue create are 422.
- The suite must run against a **fresh forge process** — repo names are fixed by the seed, so
  a second full run against the same process fails setups with 422 already-exists (the trial
  always boots a fresh entry). When restarting locally, confirm the old process is really
  dead and the port free: a successor that hits EADDRINUSE stays alive (the uncaughtException
  guard) without listening, and the stale process keeps answering.

## Round 2 — GraphQL (`/api/graphql`) and MCP (`/mcp`)

- **GraphQL engine**: hand-written tokenizer/parser/executor in `main.ts` — operations with
  names and variable definitions, aliases, inline + named fragments, directives (parsed and
  ignored), variables, inline enum lists and input objects, and JSON-array operation batching.
  Resolvers are thin views over the store and call the REST handlers for mutations
  (createIssue/closeIssue/createPullRequest/mergePullRequest/addComment), so all three
  surfaces agree by construction.
- **Global ids** are base64 `Type:numericId` (Repository/Issue/PullRequest/IssueComment/User):
  opaque (never the plain databaseId/number), stable across reads, decoded by `node(id:)`.
- **Introspection**: a static schema table drives `__type(name:)` — `fields` for object types
  (Issue, PullRequest, Repository list every field the checks probe), `enumValues` for enums
  (SearchType lists ISSUE). Unknown fields are a 200 with an `errors` array naming the field,
  never an HTTP error; no token is a 401.
- **Issues connection**: `states` filter, `orderBy` CREATED_AT/UPDATED_AT/COMMENTS × ASC/DESC,
  cursor pagination where the cursor is base64 of the last issue number on the page;
  `pageInfo.hasNextPage/endCursor` follow the slice. Pull-request `mergeable` reuses the
  merge's per-path three-way test (MERGEABLE/CONFLICTING, UNKNOWN once merged or closed).
- **MCP**: JSON-RPC over Streamable HTTP. `server/discover` answers the modern 2026-07-28
  shape (supportedVersions, capabilities `{tools:{}}`, serverInfo both top-level and under
  `_meta`), and `initialize` answers the legacy handshake (echoes a supported revision,
  else 2025-11-25). The six tools — create_repo, get_repo, create_issue, list_issues,
  create_pull_request, merge_pull_request — are thin calls into the REST handlers, returning
  `content` text + `structuredContent`. Wire discipline: malformed JSON ⇒ HTTP 400 with
  -32700; unknown tool ⇒ -32602 (never 500); missing arguments ⇒ `isError: true` results;
  no Authorization ⇒ 401; request ids (numeric or string) are echoed verbatim, so concurrent
  calls keep their own answers; `tools/list` is a frozen constant, byte-identical across calls.

## Remaining known gaps (unchanged from round 1, unexercised by the suite)

- v0 fetch is implemented but barely exercised (the harness client negotiates v2 whenever offered).
- Tag-object wants in fetch traverse only one level (tag → target object + its tree).
