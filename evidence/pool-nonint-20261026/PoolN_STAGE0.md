# PoolN dispatch noninterference: stage 0

Read the root AGENTS Security and proof discipline, common/local rules,
historical S2 ownership/lead plan/diagnosis/interface (resolved under
docs/research/100bit-spend-path-20261013), C3-BIN 01:20 SDK trust adoption,
full Pool lifecycle scope and PoolS handoff, and coherent SInt2 workspace handoff.
Option B is adopted by the owner. No extra trust is inferred from SDK route B.

Worktree/branch: cx-pool-nonint / codex/cx-pool-nonint-20261026.
Only new PoolN_ modules and this receipt directory will change. No shipped
source edit, other worktree edit, key/funds operation or push is authorized.
Host-only source copies with appended cfg(kani) harnesses preserve production
bytes. Reuse coherent SInt2 objects; do not replay the package or full extraction.

Budget: Lean 0/100 (dependencies included), Kani 0/40. Every invocation will
record exact target, source/dependency hashes, exit, wall, peakRSS, swaps and
axioms (Lean). Each scope: MemoryHigh6G/Max8G/Swap0/Tasks64; Lean -M7000;
Rust optimized, four jobs. No unchanged timeout/OOM rerun or raised caps.

Stage 1: actual short-circuit guards and close/resize/assign exclusions, with
reachable guards and exact error/frame observations. Stage 2: handler prefixes
and alternate roles, selected dispatch and verifier admission/CPI. Stage 3:
compose the checked obligations and report any source-binding gaps explicitly.
A helper theorem will not be promoted to a full handler theorem. Existing
runtime ownership/CPI/rollback semantics remain external trust as instructed.
The ASC8 write kernel belongs to PoolW_, not this job.

Frozen inherited ELF pins (not rebuilt): default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No formal closure or security finding at admission.
