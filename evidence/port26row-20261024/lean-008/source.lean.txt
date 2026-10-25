import Port26ROW_Row
set_option autoImplicit false
noncomputable section
namespace Port26ROW
open Aeneas Aeneas.Std Result
open Port23PUSH Port25ARRAY

/-- Focused dependent failure consumer at the concrete delegation instance. -/
theorem bad_index (b : verifier.BatchedWeights) (index : Usize)
    (power : Power) (basis : U32) (bad : ¬ index.val < b.raw.val.length) :
    verifier.BatchedWeights.push concrete b index power basis =
      fail Error.arrayOutOfBounds :=
  Port23PUSH.push_bad_index concrete b index power basis bad

set_option pp.proofs false
#print Port26ROW.toK
#print axioms Port26ROW.toK
#print Port26ROW.row_four
#print axioms Port26ROW.row_four
#print Port26ROW.add_unroll
#print axioms Port26ROW.add_unroll
#print Port26ROW.range_next
#print axioms Port26ROW.range_next
#print Port26ROW.owned_four
#print axioms Port26ROW.owned_four
#print Port26ROW.fold_body_complete
#print axioms Port26ROW.fold_body_complete
#print Port26ROW.range_end
#print axioms Port26ROW.range_end
#print Port26ROW.add_body0
#print axioms Port26ROW.add_body0
#print Port26ROW.add_body1
#print axioms Port26ROW.add_body1
#print Port26ROW.add_body2
#print axioms Port26ROW.add_body2
#print Port26ROW.add_body3
#print axioms Port26ROW.add_body3
#print Port26ROW.add_tail4
#print axioms Port26ROW.add_tail4
#print Port26ROW.add_tail3
#print axioms Port26ROW.add_tail3
#print Port26ROW.add_tail2
#print axioms Port26ROW.add_tail2
#print Port26ROW.add_tail1
#print axioms Port26ROW.add_tail1
#print Port26ROW.add_tail0
#print axioms Port26ROW.add_tail0
#print Port26ROW.atRow
#print axioms Port26ROW.atRow
#print Port26ROW.put
#print axioms Port26ROW.put
#print Port26ROW.fold_unroll
#print axioms Port26ROW.fold_unroll
#print Port26ROW.fold_body0
#print axioms Port26ROW.fold_body0
#print Port26ROW.fold_body1
#print axioms Port26ROW.fold_body1
#print Port26ROW.fold_body2
#print axioms Port26ROW.fold_body2
#print Port26ROW.fold_body3
#print axioms Port26ROW.fold_body3
#print Port26ROW.fold_body4
#print axioms Port26ROW.fold_body4
#print Port26ROW.fold_tail4
#print axioms Port26ROW.fold_tail4
#print Port26ROW.fold_tail3
#print axioms Port26ROW.fold_tail3
#print Port26ROW.fold_tail2
#print axioms Port26ROW.fold_tail2
#print Port26ROW.fold_tail1
#print axioms Port26ROW.fold_tail1
#print Port26ROW.fold_tail0
#print axioms Port26ROW.fold_tail0
#print Port26ROW.fold_readback
#print axioms Port26ROW.fold_readback
#print Port26ROW.row_complete
#print axioms Port26ROW.row_complete
#print Port26ROW.toBW
#print axioms Port26ROW.toBW
#print Port26ROW.fromBW
#print axioms Port26ROW.fromBW
#print Port26ROW.carrier_roundtrip
#print axioms Port26ROW.carrier_roundtrip
#print Port26ROW.owned_push_complete
#print axioms Port26ROW.owned_push_complete
#print Port26ROW.push_complete
#print axioms Port26ROW.push_complete
#print Port26ROW.bad_index
#print axioms Port26ROW.bad_index
#print Port23PUSH.ArrayIntoIter
#print axioms Port23PUSH.ArrayIntoIter
#print Port23PUSH.verifier.BatchedWeights
#print axioms Port23PUSH.verifier.BatchedWeights
#print Port23PUSH.field.QM31
#print axioms Port23PUSH.field.QM31
#print Port23PUSH.field.CM31
#print axioms Port23PUSH.field.CM31
#print Port23PUSH.verifier.update_residue_row
#print axioms Port23PUSH.verifier.update_residue_row
#print Port23PUSH.verifier.update_residue_row_loop0.body
#print axioms Port23PUSH.verifier.update_residue_row_loop0.body
#print Port23PUSH.verifier.update_residue_row_loop1.body
#print axioms Port23PUSH.verifier.update_residue_row_loop1.body
#print Port23PUSH.verifier.BatchedWeights.push
#print axioms Port23PUSH.verifier.BatchedWeights.push
#print Port23PUSH.push_complete
#print axioms Port23PUSH.push_complete
#print S7Kani2AccumulatorLoop.BatchedWeights
#print axioms S7Kani2AccumulatorLoop.BatchedWeights
#print S7Kani2AccumulatorLoop.K
#print axioms S7Kani2AccumulatorLoop.K
#print S7Kani2OwnedRow.residue_owned
#print axioms S7Kani2OwnedRow.residue_owned
#print S7Kani2OwnedPush.push_owned
#print axioms S7Kani2OwnedPush.push_owned
#print Port25ARRAY.arrayIntoIter
#print axioms Port25ARRAY.arrayIntoIter
#print Port25ARRAY.concrete
#print axioms Port25ARRAY.concrete
#print Port25ARRAY.back_carrier
#print axioms Port25ARRAY.back_carrier
#print Port25ARRAY.back_identity
#print axioms Port25ARRAY.back_identity
#print Port25ARRAY.scalar_all_results
#print axioms Port25ARRAY.scalar_all_results
#print Port25ARRAY.fold_total
#print axioms Port25ARRAY.fold_total
#print Port25ARRAY.folded
#print axioms Port25ARRAY.folded
#print Port25ARRAY.fold_eq
#print axioms Port25ARRAY.fold_eq
#print Port25ARRAY.product_total
#print axioms Port25ARRAY.product_total
#print Port25ARRAY.total_fold_order
#print axioms Port25ARRAY.total_fold_order
#print Aeneas.Std.Array.to_slice_mut
#print axioms Aeneas.Std.Array.to_slice_mut
#print Aeneas.Std.Array.from_slice
#print axioms Aeneas.Std.Array.from_slice
#print Aeneas.Std.core.slice.Slice.iter_mut
#print axioms Aeneas.Std.core.slice.Slice.iter_mut
#print Aeneas.Std.core.slice.iter.IteratorIterMut.next
#print axioms Aeneas.Std.core.slice.iter.IteratorIterMut.next
#print Aeneas.Std.alloc.vec.Vec.set
#print axioms Aeneas.Std.alloc.vec.Vec.set
end Port26ROW
end
