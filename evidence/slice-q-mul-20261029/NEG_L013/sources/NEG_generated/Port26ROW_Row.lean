import Port26ROW_Add
import Port26ROW_Fold
import Port23PUSH_Frame
set_option autoImplicit false
noncomputable section
namespace Port26ROW
open Aeneas Aeneas.Std Result
open Port23PUSH Port25ARRAY

/-- Complete mutable source row with the content delegation instance, on every
full four-word carrier. Checked add failures and div are preserved; total folds
commute across checked later lanes because they introduce no failure/effect in
this pure Result interpretation. Native association/effects are separate. -/
theorem row_complete (row : Row) (power : Power) (basis : U32) (flush : Bool) :
    verifier.update_residue_row concrete row power basis flush =
      S7Kani2OwnedRow.residue_owned row (toK power) basis flush := by
  rcases row_four row with ⟨a,b,c,d,rfl⟩
  rw [owned_four]
  change (do
    let row1 ← verifier.update_residue_row_loop0 ⟨0#usize,4#usize⟩
      (Array.make 4#usize [a,b,c,d]) basis
      (Array.make 4#usize [power.c0.a,power.c0.b,power.c1.a,power.c1.b])
    if flush then
      (do let (it,back) ← concrete row1
          let f ← verifier.update_residue_row_loop1 it id
          ok (back f))
    else ok row1) = _
  rw [add_tail0]
  simp only [bind_assoc_eq,bind_tc_ok]
  congr 1
  funext x0
  congr 1
  funext x1
  congr 1
  funext x2
  congr 1
  funext x3
  cases flush with
  | false => rfl
  | true => exact fold_readback x0 x1 x2 x3

/-- Exact carrier conversion: all raw rows, terms and four power words. -/
def toBW (b : verifier.BatchedWeights) : S7Kani2AccumulatorLoop.BatchedWeights :=
  ⟨b.raw,b.terms⟩
def fromBW (b : S7Kani2AccumulatorLoop.BatchedWeights) : verifier.BatchedWeights :=
  ⟨b.raw,b.terms⟩

theorem carrier_roundtrip (b : verifier.BatchedWeights) : fromBW (toBW b) = b := by
  cases b
  rfl

/-- Unconditional owned outer normalization. No safe domain or successful row
execution is assumed. Indexing before mutation preserves invalid-index failure. -/
theorem owned_push_complete (b : S7Kani2AccumulatorLoop.BatchedWeights)
    (index : Usize) (power : S7Kani2AccumulatorLoop.K) (basis : U32) :
    S7Kani2OwnedPush.push_owned b index power basis =
      (do let row ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row)
            b.raw index
          let updated ← S7Kani2OwnedRow.residue_owned row power basis
            ((b.terms &&& 3#usize) = 3#usize)
          ok {b with raw := b.raw.set index updated}) := by
  by_cases bound : index.val < b.raw.val.length
  · obtain ⟨row,hr,_⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.index_usize_spec b.raw index bound)
    obtain ⟨⟨old,back⟩,hm,_,hback⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.index_mut_usize_spec b.raw index bound)
    have hr' : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row)
        b.raw index = ok row := hr
    have hm' : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Row)
        b.raw index = ok (old,back) := by
      rw [alloc.vec.Vec.index_mut_slice_index]
      exact hm
    simp only [S7Kani2OwnedPush.push_owned,hr',lift,bind_tc_ok,hm',hback]
    all_goals rfl
  · simp [S7Kani2OwnedPush.push_owned,alloc.vec.Vec.index,
      core.slice.index.SliceIndexUsizeSlice,alloc.vec.Vec.index_usize,
      Slice.index_usize,bound]

/-- Actual mutable source-emitted push equals the owned source push under exact
carrier conversion, including full Results and the entire Vec.set/terms frame.
The explicit collection delegation is derived; native association is separate. -/
theorem push_complete (b : verifier.BatchedWeights) (index : Usize)
    (power : Power) (basis : U32) :
    verifier.BatchedWeights.push concrete b index power basis =
      (do let out ← S7Kani2OwnedPush.push_owned (toBW b) index (toK power) basis
          ok (fromBW out)) := by
  rw [Port23PUSH.push_complete,owned_push_complete]
  simp only [row_complete,bind_assoc_eq,bind_tc_ok,toBW,fromBW]
  all_goals rfl

#print axioms row_complete
#print axioms toBW
#print axioms fromBW
#print axioms carrier_roundtrip
#print axioms owned_push_complete
#print axioms push_complete
end Port26ROW
end
