# LOG D387 resume handoff — V244 deployed-toolchain gate

Exact worktree `/Users/dominic/ZK/.worktrees/pv-b3p6`, unchanged branch
`codex/pv-b3p6-20261028`, entry `9539b7530bf5d364a0c363c768f0c95970905758`.
Rust differential/extraction source revision
`98d809dde3214eecc8f686b83df734606c34f598`.
Prior accepted handoff: [FINAL-D377.md](FINAL-D377.md).
Resume commits: [COMMIT-LOG-resume4.txt](COMMIT-LOG-resume4.txt).

**V244 remains OPEN. V228/V229/V243 retain accepted CLOSED status.
V241/V245 remain OPEN and unchanged. Target not yet established.**

Stop/handoff: pinned extraction infrastructure cannot meet the explicit
rustc 1.94.1/std requirement. The actual attempt failed E0514: pinned Charon
uses rustc 1.98.0-nightly, incompatible with the required 1.94.1 std.
[Exact finding and governing boundary](TOOLCHAIN-BLOCK-resume4.md).
No nightly-std fallback, extractor rebuild/replacement, or Kani was used.
No checked counterexample to a ledger row or endpoint was found.

Fresh budget remains **100 Lean attempts, 0 Kani**: zero Lean compiles and
zero Kani runs launched; all IDs 42000–42099, including audits 42097–42099,
remain unused. No Lean import was attempted, so no external-object replay
preflight or axioms audit is claimed for this resume. The requested final
combined audit and focused closure replay await a completed row proof.

## V244 work and exact validation scope

Five owned files under `tools/pv-b3p6-20261028/v244/` byte-equal the shipped
host terminal, copy-terminal and field helpers and generated constants.
[Source pins](source244-resume4.json) and
[structural preparation](structural227-resume4.json) retain hashes and cfg
selection. This is preparation for the plain **structural** route, not a
completed native/source/selected-callback law. No new theorem is claimed.
The complete-Result Lean law, original-carrier installation, all other-field
frames and nonvacuity are still missing; the runjoin op227 hypothesis remains.

The native differential is a release **binary**, with cfg(test)=false, rather
than a unit test that would select extra test-only helper bodies. It compares
complete same-input Results across the shipped deployed host, the byte-identical
owned host copy and the statement implementation. The final run checks
64 cases: both public variants, 16 canonical arbitrary-claim/challenge seeds,
and valid/invalid append increments. It observes **32 Ok and 32 Error::Public**
and also checks perturbations of all three omitted D-column claims.
This is **finite validation**, not universal equality or source refinement.

The first retained 64-case run passed but produced only successes: its
next-root mutation is not rejected by the terminal. That coverage gap was
corrected by changing the differential source to violate the actual append
increment guard and asserting the expected 32/32 split. This justified the
second native run; no unchanged regression was repeated.

[Deployed configuration](features227-resume4.json): rustc 1.94.1, release,
opt-level 3, overflow checks/debug assertions off, no cfg(test), deployed
`tools/r1-cost-probe` root features `r1p-check` and
`aspis-r1-cost-probe/ct-host-prover`. Every validation dependency matches a
deployed node's name, version, source and complete feature list, with zero
feature differences. The record includes every resolved crate, both lock
hashes and 1,943 std-source hashes. Preliminary graph snapshots retain the
compile-free work that added explicit parity dependencies before launching
any native gate. All 706 frozen source/configuration files were checked on
the host against this worktree before gate launch. Initial absent files and
an older host lockfile were synchronized only into this job's own workspace.

## Receipts and remaining obligations

All three runs used one own capped scope at a time, MemoryHigh 6G,
MemoryMax 8G, MemorySwapMax 0, TasksMax 64, with successful admission.
No refusal, transport retry or memory kill occurred.
[Receipt index](receipt-index-resume4.json) links exact commands, revisions,
admission logs and resource measurements; #print axioms is N/A for Rust runs.

|Target|Exit|Wall seconds|Peak RSS KiB|Swap|
|---|---:|---:|---:|---:|
|native227-resume4, initial success-only coverage|0|46.982|544132|0|
|native227-resume4-errors, final 32/32 Result coverage|0|0.174|136048|0|
|charon227-deployed-resume4, incompatible std|101|0.128|58944|0|

Before/after: no row or full endpoint premise was removed, added, weakened,
or moved into T in this resume. T remains exactly entropy_law, entropy_kernel,
observation. V165/V167, E1/E2, real RunJoin, client proof-account routing and
L1/L2/L3 remain substantive. Simulator and observer are unchanged. No new
Kani PASS, including quarantined copy/function-pointer evidence, is credited.

No files under crates/ or programs/, other worktrees, shared sources or keys
were changed; no merge or push. The only source synchronization was into this
job's own host workspace. [Cache cleanup](resume4-cleanup.json) records disposal
of this job's rebuildable Rust output directories after all scopes ended;
source, hashes and receipts are retained.

Next concrete deliverable: the lead supplies an approved pinned extraction
path compatible with rustc 1.94.1 and its std sources, resolving the conflicting
constraints without silently changing configuration. Then extract the owned
V244 reference, prove its complete Result law, install op227 in the original
carrier with all other fields framed, prove nonvacuity and discharge the
runjoin bridge's exact selected-callback hypothesis. Finish V244, then V241,
then V245; combined audit and focused closure replay last.
