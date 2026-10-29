# D438 plan and qualification boundary

Worktree `/Users/dominic/ZK/.worktrees/pv-own`, branch `codex/pv-owng-20261029`, base `4d2d31fa4f`. No implementation edits. Budgets Lean60/native30/Kani0; IDs63700–63799, audits63797–63799.

1. Revalidate inherited source pins. Cut traversal at alloc/realloc/dealloc, including all libc internals. The previous single-threaded/errno objections are withdrawn under own-2''.
2. Review every outside-box read/call and pointer-derived decision, including compiler-generated runtime calls. Do not confuse prover-local host_forest fixed arrays with the assigned original statement Vec roots.
3. If qualification holds, compose named original op133/mask value lemmas into explicit Results, execute the appropriate deployed release roots, byte-compare and fingerprint-cross-check, record allocation/abort under rdea-1, audit and replay once.
4. If qualification fails, retain an exact source/artifact witness and report the failed condition without claiming a witness-dependent privacy finding or restoration. Continue independent evidence work.

Native inspection probe: reuse pinned optimized Rust rlibs read-only, without changing another workspace. Compilation/linking is the expected work; no heavy arithmetic. Scope caps6G/8G/no swap/Tasks64. Scope admission must exit0 and say allowed:true in the launch shell, plus in-scope barrier. No uncapped native execution.
