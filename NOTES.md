# Forge notes — round 1 (17 Nov 2026)

Single-file implementation in `main.ts` (Node stdlib only, type-strippable TS, in-memory store).

## Verified locally (fresh process, kit runner `sdk/run.ts --perf`)

| group    | result |
| -------- | ------ |
| git      | 30/30  |
| repos    | 15/15  |
| issues   | 15/15  |
| pulls    | 20/20  |
| protocol | 5/5    |
| graphql  | 0/20 — round 2, not started |
| mcp      | 0/15 — round 2, not started |

Perf medians (3 rounds each; calibration references in parentheses):
push 686 ms (~1641), clone 100 ms (~267), read 582 ms (~2760), write 110 ms (~349)
→ perf column 180/200, feature column 425/600, total 605/1000 on this machine.

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
  always boots a fresh entry).

## Round 2 remainder

- GraphQL endpoint (20 checks): viewer/repository/issue/pull queries, mutations, node ids,
  introspection — the store already holds everything it needs.
- MCP endpoint at `/mcp` (15 checks): JSON-RPC initialize/server-discover/tools over the same
  store.
- Possible hardening: v0 fetch is implemented but barely exercised by the suite (the harness
  client negotiates v2 whenever offered); tag-object wants in fetch only traverse one level
  (tag → target object + its tree), which no round-1 check exercises beyond ls-refs peeling.
