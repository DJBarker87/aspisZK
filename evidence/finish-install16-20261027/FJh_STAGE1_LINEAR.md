# Native internal-linear value

FJh_InternalLinearExact.source_success is checked at FJh_023: for every
canonical native 16-lane state, the actual FIq_Native internal_linear_lazy
returns a canonical native state whose every decoded lane equals
R0P.poseidonInternalLinear on those SAME input cells. No native output or
intermediate callback value is a hypothesis. Each traversal is a symbolic
fuel induction, not concrete whole-loop evaluation.

This is the linear predecessor within step1, not the completed internal pair.
No top-level premise is removed. Rc10 and separate FIr before/after statements,
carriers and conclusions remain identical; both ledger deltas 0T/0P/0G/0C.
Inherited conditional non-vacuity is preserved; no unconditional satisfying
fixture is claimed.

FJh_023: lake env lean -j1 -M7000 -DElab.async=false -o
FJh_InternalLinearExact.olean FJh_InternalLinearExact.lean; exit0;
wall1.917734296002891s; peak3858224KiB; swap0; source revision
ed0aa6ae4a4fd801ba8eb0cb8dafa495caa0e14e plus exact dirty-source and dependency
hashes in receipt. Printed axioms: propext, Classical.choice, Quot.sound.
All new predecessors have their own printed axiom audits and exact receipts.
Every run used reservation admission and one scope, 6G high/8G max/swap0/
tasks64. No shipped or other-prefix file changed; no ELF rebuild triggered.
Failed dependency/preflight and corrected typing attempt are retained.

Next: round value, actual selector map, literal constants and native seven-term
dots, then SAME interpolated pair value. Budget through023:23 charged Lean,
0 Kani; no timed-out/memory-killed job and no package replay.
