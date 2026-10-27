# Installed point body checked

FJf_PointCell.value_step proves values, complete frame and canonicality for ONE
actual installed weights_new_loop0_loop0.body iteration. The operands are
read from the SAME points array and the actual TAU-selected coordinates.
FJd_SourceFactor.value is imported and applied, not reproved. The reference
run is derived by body inversion; no per-iteration equality premise is added.
The mutable-array continuation comes from the actual index_mut call.

Exact checked dependencies: FJf_PointBody.source, FJf_ArrayOps.*, FJf_ArraySlots.*,
FJf_PointIndices.tau_read, FJf_Coordinates.indices, FJf_FactorArray.* and
FJf_DigitValue.value. Full printed axioms in per-attempt receipts use only
propext/Classical.choice/Quot.sound or subsets. Failed diagnostic axioms with
sorryAx are excluded; no such source is delivered as a checked result.

15/100 Lean attempts (9 passing, 6 failed), 0/20 Kani. No timeout or memory kill,
no changed cap, no package replay. All starts use one admitted scope with
6G/8G/swap0/tasks64 and Lean -M7000. Each receipt records the exact command,
source/dependency hashes, revision, exit, wall time, RSS, swap and axiom lines.
No installed complete part meaning or top-level premise removal yet: 0/7,
ledger delta 0T/0P/0G/0C. The next target is inner five-digit induction.
