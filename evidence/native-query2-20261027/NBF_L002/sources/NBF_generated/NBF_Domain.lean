import NBF_Frame
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_Domain
open S7Kani2AccumulatorLoop (BatchedWeights K)
open S7Kani2OwnedRowRefinement (makeRow powerLimb)
/-- The reached cursor invariant establishes the row leaf's exact phase domain.
The SAME indexed read supplies the four row words. -/
theorem row_domain (weights : BatchedWeights) (index : Usize) (x : Fin 4 → U64)
 (inv : NBB_Sweep.Inv weights.terms.val index.val weights.raw)
 (read : weights.raw.val[index.val]?=some (makeRow x)) :
 ∀ k, NBB_Phase.Bound weights.terms.val (x k).val := by
 have bound := inv index.val (makeRow x) read
 have own : NBB_Sweep.Bound weights.terms.val (makeRow x) := by
   simpa only [Nat.lt_irrefl,if_false] using bound
 intro k
 apply own (x k)
 fin_cases k <;> simp [makeRow,Array.make]

/-- Every call to the inherited source theorem discharges the phase premise
from that reached cursor, rather than assuming a stronger per-row bound. -/
theorem push (weights : BatchedWeights) (index : Usize) (power : K)
 (basis : U32) (x : Fin 4 → U64)
 (inv : NBB_Sweep.Inv weights.terms.val index.val weights.raw)
 (read : weights.raw.val[index.val]?=some (makeRow x))
 (nativeRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice S7Kani2OwnedRow.Row)
   weights.raw index=ok (makeRow x))
 (hc : ∀ k, (powerLimb power k).val<2^31-1) (hb : basis.val<2^31-1) :
 ∃ y : Fin 4 → U64,
 S7Kani2OwnedPush.push_owned weights index power basis=
   ok {weights with raw:=weights.raw.set index (makeRow y)} ∧
 NBB_Sweep.Inv weights.terms.val (index.val+1)
   (weights.raw.set index (makeRow y)) ∧
 (∀ j, j≠index.val →
   (weights.raw.set index (makeRow y)).val[j]?=weights.raw.val[j]?) := by
 have inRange := (List.getElem?_eq_some_iff.mp read).1
 obtain ⟨y,run,value,done⟩ := NBB_Push.source weights index power basis x
   inRange nativeRead hc hb (row_domain weights index x inv read)
 exact ⟨y,run,NBB_Push.sweep weights index (makeRow y) inv done,
   fun j different => NBF_Frame.set_frame _ _ _ _ different⟩

#print axioms row_domain
#print axioms push
end NBF_Domain
