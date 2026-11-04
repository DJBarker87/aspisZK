# PV_RDCD5 — V233 and V236 restored; V197 finding

Branch `codex/pv-rdcd5-20261101`, exact worktree `/Users/dominic/ZK/.worktrees/pv-rdcd3`, base **ba1fa07d9e**.
Resumed D555 head **af37279448**. Reporting source revision `27c08444d2259e00727babde8bdc3cbfc0bfd4e4`;
[commit log](COMMITS.txt). No merge or push. The lead-recreated host flag was
read and satisfied; historical D541 gate polls were not repeated.

| Row | Final result at the existing qualified boundary |
|---|---|
| V197 | **FINDING** — [kernel-checked counterexample](V197-FINDING.md): existing `ProverRwSuccessParserSource…QM31.from_le_bytes` on empty Slice returns `fail.panic`; owned `BytesSource.qm []` returns `fail.arrayOutOfBounds`. `PV_RDCD5_ParserErrors.carrier_mismatch` passes78213. Literal arbitrary-slice whole-Result identification is false. No eager16-byte guard, success-only equality, error erasure or restoration is substituted. |
| V233 | **RESTORED / B** — `PV_RDCD5_V233.consumed_instance` discharges existing `PV_AL_SplitSelected.consumed` for the original Eager64 typed family and every valid input Slice. Generic storage inverse, wrapper roundtrip/injectivity, pointer/count/tail and exact typed Result association pass. [Before/after and evidence](V233-ASSOCIATION.json). |
| V236 | **RESTORED / B** — `PV_RDCD5_V236.op216_instance` discharges existing `UpdateCarrier.value` / `UpdateSelected.selected_native` at original safe Eager64 `length64/pos<64` domain. Every branch, cursor, dead byte, ordered Result callback and typed batch is retained; only the original core callback stays parametric. No singleton-fold premise. [Before/after and evidence](V236-ASSOCIATION.json). |

All seven committed drafts compile, plus ParserErrors and UpdateSplit. The
three local parser drafts are valid owned-model proofs; they do not restore the
false V197 callback identification. Its counterexample was independently
replayed in the final release targets. V233 typed association uses
`BlockCarrier.encode_flatten/flatten_injective`, `V233.typed_roundtrip` and
`UpdateSplit.typed_batches/compression_instance`, rather than byte equality alone.

[Coherence](final-coherence/receipt.json) passes:70 project objects, all5673
unchanged h4 external hashes,37 successful actual-launch fingerprints and26
native source pins; exit0, wall0:01.76, peak45684KiB, swap0. [Detailed result](coherence-result.json).
33 project objects were reused only after original source/import/toolchain/
prefix checks, in namespace-complete plain-copy overlays;37 were built fresh.
No Stream A object or shared-source overwrite. [Release-object addendum](release-object-addendum.json)
records the3 new audit objects and verifies the final launch fingerprint,
completing the73-project-object cohort without a second manifest replay.

The required sequence ran once and passed:

| Target/receipt | Exit | Wall | PeakRSS KiB | Swap |
|---|---:|---:|---:|---:|
| [Combined statement/axioms 78297](lean-78297/receipt.json) | 0 | 0:01.51 | 2572600 | 0 |
| [Focused typed replay 78298](lean-78298/receipt.json) | 0 | 0:01.22 | 2576448 | 0 |
| [Single frozen manifest 78299](lean-78299/receipt.json) | 0 | 0:01.22 | 2569476 | 0 |

The combined audit checks123 full declaration types/axioms; focused and final
replays each query3 exact interfaces, including the finding. Only
propext/Classical.choice/Quot.sound occur. [RUNS.json](RUNS.json) records every
exact command, source revision/hash/blob, import fingerprint, exit, wall,
peakRSS, swap and complete printed-axiom lines, including retained failures.

Actual budget: **44/100 Lean (40 pass,4 fail),
4/30 capped native (all pass),0 Kani**. Uncredited failures78206,
78207,78233,78237 were elaboration errors; source changed before each retry.
Their sorryAx diagnostics are failed elaborations, not admitted source axioms.
[Protocol audit](release-protocol-check.json):48 actual scopes, minimum launch
gap186.054967s, zero void launches,
three uncharged refusals (two cgroup ENOENT races, one aggregate reservation).
Each waited the full cooldown and retried the same unlaunched target/ID.
Caps6G/8G/swap0/Tasks64, Lean-M7000 throughout; no scope raised its cap.
Quiet-window markers were read-only; the final recorded marker is expired.

Source bindings use own-1/k-prime structural arguments at the existing
compiler/runtime boundary, plus complete kernel-checked carrier/Result laws.
[Deployed configuration reuse](deployed-config-reuse.json) preserves the
unchanged1.94.1 release recipe and487-package resolved feature graph.
Historical native differentials remain finite validation and were not rerun.
No Rust build, Kani verification/re-credit, extraction or new translator was
used. No Aeneas.Std fmt credit or new generated-declaration unification is
claimed; ae1,fmt-1,k3 and dup-1-prime boundaries remain.

Endpoint premises removed/added/changed: **zero**. Before/after exact row
statements and qualifications are in the two association files. T stays
exactly entropy_law/entropy_kernel/observation. V370/D381/D386, E1/E2, real
RunJoin, world/physical observer, client route and L1/L2/L3 remain obligations.
No production source, dictionary, simulator, observer, soundness file or key
was modified. The privacy target is not established.

[Cleanup](cleanup-result.json) removed only this task's verified compiler
caches (4,625,912,152 bytes), after all gates;
sources, receipts and all evidence inputs remain. Object hashes describe the
measured pre-cleanup files; those private caches are no longer available.
No task process remains running. Stop basis: V197's checked counterexample;
the other two assigned links and final release checks are complete.56 ordinary
IDs remain unused. Next deliverable is an explicitly faithful V197 error model
and complete arbitrary-slice transport to the existing parser, preserving panic,
None, late checks and the physical-observer obligation.
