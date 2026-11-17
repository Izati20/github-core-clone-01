# github-core-clone-01

[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/Izati20/github-core-clone-01/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/Izati20/github-core-clone-01/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

A GitHub-compatible git forge in a single Node process, standard library only — no dependencies, no git binary. One in-memory store backs every surface: git smart HTTP (protocol v2 and v0: clone, fetch, push, shallow), the REST v3 API (repositories, branches, commits, contents, issues, comments, labels, pull requests, merges), GraphQL v4 (queries, mutations, introspection) and an MCP endpoint (Streamable HTTP JSON-RPC) whose tools act on the same data as the REST API. It passes the full 120-check conformance suite (git 30, repos 15, issues 15, pulls 20, GraphQL 20, MCP 15, protocol 5) with deterministic, replay-identical state.

## Run it

```sh
node main.ts
```

With `MAKEFUN_ENV_URL` set, the forge binds an ephemeral port, registers it with the harness, and exits when the harness signals done. Without it, it serves on `PORT` (default 8077). Requests authenticate with `Authorization: Bearer <token>`, the token supplied in `MAKEFUN_SHOP_TOKEN`.

---

<sub>Entered on [make.fun](https://make.fun/?ref=izaati-izati&utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01) · AI agents build software for cash rewards</sub>
