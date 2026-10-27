import NBB_Row
import NBB_Sweep
import S7Kani2OwnedPushModel
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBB_Push
open S7Kani2AccumulatorLoop (BatchedWeights K)
open S7Kani2OwnedRowRefinement (makeRow powerLimb)
/-- Total owned Vec push and SAME row-phase advance. There is no successful
callee assumption and no restriction on the other raw rows. -/
theorem source (weights : BatchedWeights) (index : Usize) (power : K)
 (basis : U32) (x : Fin 4 → U64)
 (hi : index.val<weights.raw.length)
 (read : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice S7Kani2OwnedRow.Row)
   weights.raw index=ok (makeRow x))
 (hc : ∀ k, (powerLimb power k).val<2^31-1) (hb : basis.val<2^31-1)
 (phase : ∀ k, NBB_Phase.Bound weights.terms.val (x k).val) :
 ∃ y : Fin 4 → U64,
 S7Kani2OwnedPush.push_owned weights index power basis=
  ok {weights with raw:=weights.raw.set index (makeRow y)} ∧
 (∀ k, (y k).val=AspisR1BatchedFoldSourceStep.sourcePush weights.terms.val (x k).val
   ((powerLimb power k).val*basis.val)) ∧
 NBB_Sweep.Bound (weights.terms.val+1) (makeRow y) := by
 obtain ⟨y,run,value,bounds⟩ := NBB_Row.source x power basis weights.terms.val hc hb phase
 have row : S7Kani2OwnedRow.residue_owned (makeRow x) power basis
  ((weights.terms &&& 3#usize)=3#usize)=ok (makeRow y) := by
  simpa only [S7Kani2OwnedPushModel.phase_flag] using run
 refine ⟨y,S7Kani2OwnedPushModel.push_of_row weights index power basis _ _ hi read row,value,?_⟩
 intro word mem
 simp only [makeRow,Array.make,List.mem_cons,List.not_mem_nil,or_false] at mem
 rcases mem with rfl|rfl|rfl|rfl <;> exact bounds _

/-- The row cursor moves without incrementing the transaction's term count. -/
theorem sweep (weights : BatchedWeights) (index : Usize) (row : S7Kani2OwnedRow.Row)
 (inv : NBB_Sweep.Inv weights.terms.val index.val weights.raw)
 (done : NBB_Sweep.Bound (weights.terms.val+1) row) :
 NBB_Sweep.Inv weights.terms.val (index.val+1) (weights.raw.set index row) :=
 NBB_Sweep.update weights.terms.val index.val weights.raw row index rfl inv done
#print axioms source
#print axioms sweep
end NBB_Push
