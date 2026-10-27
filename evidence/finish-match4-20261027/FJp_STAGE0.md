# FJp L143 continuation

Branch codex/cx-finish-match4-20261027; base d0bdff6733a070aaf18fd91360b0641a49b3366b.
Adopted top: AspisR1.ARX_Root.deployed. Only L143 native-local and
F3Y_G_L143 are in scope. FJm/FJn rows and all predecessor modules are read-only.

Read the repository Security and proof discipline, common/local Lean rules,
S2 handoff/plan/diagnosis/interface, C3-BIN route-B ruling, owner contract
amendments, SInt2 coherent workspace handoff, FIr handoff/rows, FJo
handoff/rows/obstruction and the relevant FJo/FJl/FJi proof sources.
The abbreviated initial handoff paths resolve under
`docs/research/100bit-spend-path-20261013/`.

Budget 100 Lean attempts including dependencies, 20 Kani runs. No package
replay. One own host scope at a time, -M7000, MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64, existing S2W launcher and
reservation gate only. Prefix-specific orchestration reuses FJo's unchanged
launcher invocation and SInt2 object selection; it is not new infrastructure.
Receipts retain target/command, source revision/hash, direct dependency
fingerprint, status, wall/RSS/swap and complete axioms/errors.

Stage 1 first replaces the failed multi-rewrite with four individually
checked generic coordinate transports and a generic equality chain.
FJp_001 and 004 pass; 002 is an unresolved operand, 003 default-heartbeat
failure in the concrete query wrapper. No option/cap changed, and 003 was
replaced by the generic equality chain, not rerun unchanged. Pending work
is concrete per-query application, Fin22 induction, native installation,
collision-aware global installation and ARX propagation.

No top premise removal is credited yet. No shipped/cfg(kani) change,
Rust/Kani/SBF/release replay, wallet/key operation, push or merge.
