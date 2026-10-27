# Frozen implementation and artifact scope

No shipped Rust source, cfg(kani) harness, wire format, feature configuration,
release ELF, wallet or key changes in this job. No Rust, Kani or SBF gate runs.
The conditional ELF rebuild trigger therefore does not fire. These are inherited
release pins, not freshly reproduced ELF hashes:

- default: f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet: 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool: 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

All compilations use the existing coherent replay workspace
/home/dombarker/project-offloads/codex-cx-replay-dry-20261026 and Lean 4.32.0.
Exact source hashes/revisions, selected direct object hashes, command, exit,
wall seconds, peak RSS KiB, swaps, scope limits, full #print axioms and raw output
are retained in each attempt receipt and indexed in RPv_attempts.jsonl.
The complete predecessor toolchain/library audit is inherited; direct object,
sidecar and tool pins are rechecked. This does not establish D188 producer/body
association or source-to-ELF equivalence. The source snapshots are import-only
continuation contexts, not a changed protocol or a source-adoption decision.

Only evidence/replay-tops3-20261027 is written in the local worktree. Sources
and job scripts use RPv_ names. Other workers' branches/worktrees/candidate
files are not edited. No binary, object, ELF or archive enters git. The accepted
source-context objects remain in the one pinned continuation cache; completed
own query-only objects are eligible for recorded cleanup after final checking.
