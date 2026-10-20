# Actual S3 loop-1 inner-prefix result (v5)

This packet records a focused Lean 4.32 result for successful executions of the
actual generated weights.s2_grouped_inactive_pair_loop1_loop0 body loop. It
shows that a successful 16-entry inner loop, starting from canonical zero and
the actual enumerator/slice cursor state, returns a canonical field element
whose decoded value is the selected-mask prefix sum.

The theorem is conditional on successful loop execution and canonicality of
the 16 input elements. It does not establish loop totality or the outer
12-group accumulation. The outer source constructs the iterator through
Array.to_slice, Slice.iter, and enumerate; that setup is being proved in a
separate focused target.

The packet includes the exact target source, accepted receipts/logs, and direct
Lean source owners. OLean objects are intentionally not included. Native
object paths and SHA256 pins are in manifest.json.
