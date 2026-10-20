# S3 actual loop-0 success readback

This focused Lean result proves success inversion for the actual grouped-pair accumulator path. A successful `weights.s2_grouped_inactive_pair` execution forces each index `0..63` through the real loop-0 callback, and each successful callback decode is tied to `weights.field` on the same bytes and index, including its computed 32-byte slice and `from_le_bytes` result. The proof retains a precise per-index read witness; it does not claim helper totality or prove that arbitrary input bytes make the full helper succeed.

The main theorem is `AspisR1GroupedPairActualFieldOpsV3.ActualLoop0SuccessReadback.grouped_pair_success_supplies_parser_reads`. It is compiled under Lean 4.32 with default proof options and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The exact direct parser bridge source and producer receipt are pinned to sibling packet `../s3-actual-field-parser-readback-v1-20261020/`. The Aeneas `RangeIter` import is pinned by source snapshot and object hash; it is a library proof helper.

The `attempts/accepted-v1` directory retains exact command, preflight, Lean output, timing, resource receipt, admission proof, and runner scripts. No `.olean` or other compiled binary is included.
