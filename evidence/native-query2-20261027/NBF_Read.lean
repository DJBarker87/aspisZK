import NBF_Domain
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_Read
open S7Kani2AccumulatorLoop (BatchedWeights K)
open S7Kani2OwnedRowRefinement (makeRow powerLimb)
/-- The actual checked Vec read follows from the SAME list observation;
it is no longer a separate caller-supplied success. -/
theorem indexed (raw : NBF_Frame.Raw) (index : Usize) (row : NBF_Frame.Row)
 (read : raw.val[index.val]?=some row) :
 alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice NBF_Frame.Row)
   raw index=ok row := by
 have hi := (List.getElem?_eq_some_iff.mp read).1
 obtain ⟨value,run,hvalue⟩ := WP.spec_imp_exists
   (alloc.vec.Vec.index_usize_spec raw index hi)
 have eq : value=row := by
   have get : raw.val[index.val]?=some value := by
     rw [List.getElem?_eq_getElem hi]
     exact congrArg some hvalue.symm
   exact Option.some.inj (get.symm.trans read)
 rw [alloc.vec.Vec.index_slice_index]
 simpa only [eq] using run

theorem push (weights : BatchedWeights) (index : Usize) (power : K)
 (basis : U32) (x : Fin 4 → U64)
 (inv : NBB_Sweep.Inv weights.terms.val index.val weights.raw)
 (read : weights.raw.val[index.val]?=some (makeRow x))
 (hc : ∀ k, (powerLimb power k).val<2^31-1) (hb : basis.val<2^31-1) :
 ∃ y : Fin 4 → U64,
 S7Kani2OwnedPush.push_owned weights index power basis=
   ok {weights with raw:=weights.raw.set index (makeRow y)} ∧
 NBB_Sweep.Inv weights.terms.val (index.val+1)
   (weights.raw.set index (makeRow y)) ∧
 (∀ j, j≠index.val →
   (weights.raw.set index (makeRow y)).val[j]?=weights.raw.val[j]?) :=
 NBF_Domain.push weights index power basis x inv read
   (indexed weights.raw index (makeRow x) read) hc hb
#print axioms indexed
#print axioms push
end NBF_Read
