# Actual begin challenges and active-literal canonicality

The checked terminal arithmetic consumer now derives μ and zc canonicality from the same actual begin execution and field-copy bridge. It no longer takes independent canonicality premises for those two challenges. The endpoint remains conditional on the other composition/H1/copy/point-callback hypotheses visible in its source; no whole terminal refinement is claimed.

Two additional checked results advance the current `active_literal` path. The concrete sparse 6144 mask produces a canonical sum, reusing the 4096 subcase. The actual outer-loop induction preserves canonicality provided each block satisfies `maskStepOK`. The full constant-table proof discharging that premise remains OPEN. The generic selector-loop drafts failed and are retained as failed diagnostics, not accepted theorems. This work does not touch the held commitment layer.

| Focused target | Exit | Wall seconds | Peak process RSS bytes | Process swaps |
| --- | --- | --- | --- | --- |
| Actual begin μ/zc terminal consumer V2 | 0 | 39.08 | 2,684,485,632 | 0 |
| Sparse mask 6144 canonicality | 0 | 5.51 | 2,263,515,136 | 0 |
| Mask canonicality axiom audit | 0 | 5.75 | 2,191,785,984 | 0 |
| Actual outer active-loop induction | 0 | 12.00 | 2,212,446,208 | 0 |
| Outer-loop axiom audit | 0 | 22.09 | 2,122,792,960 | 0 |

All printed green axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`. Receipts retain exact source revisions, source/object/direct-import hashes, full ordered `LEAN_PATH`, compiler version, commands and aggregate-memory monitoring. These were focused local Lean 4.32 checks below 4 GiB aggregate Lean limits; the machine already had approximately 16.7 GiB of system swap in use. Zero process swaps is not a cgroup swap exclusion or a claim that the whole machine used no swap. No full manifest replay was run.

Publication validated all 46 files in `SHA256SUMS`, all five successful receipts and exact readable source copies. The immutable archive SHA256 is `e799c56460b3549448b5cb550f9242bd3c50f894ad37d5cc6476cc368e7629f1`; SHA256SUMS SHA256 is `307dbd7ee7479133991c87b5c58bd5eab6cd84c8b359f4183b7f2ef05ec77fa8`. The archive includes objects, frozen proof/audit sources, logs, receipts and failed selector induction v4–v6. Readable sources are in `lean-candidates/current-terminal-arithmetic-20261019`.
