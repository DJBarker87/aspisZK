import NBB_Phase
import S7Kani2OwnedRowRefinement
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBB_Row
open S7Kani2OwnedRowRefinement
/-- Total four-limb emitted transition and its next phase, on arbitrary inputs
satisfying the actual canonical/periodic caller invariant. -/
theorem source (x : Fin 4 → U64) (power : S7Kani2OwnedRow.K)
 (basis : U32) (terms : Nat)
 (hc : ∀ j, (powerLimb power j).val<2^31-1)
 (hb : basis.val<2^31-1) (hp : ∀ j, NBB_Phase.Bound terms (x j).val) :
 ∃ y : Fin 4 → U64,
 S7Kani2OwnedRow.residue_owned (makeRow x) power basis (decide (terms%4=3))=ok (makeRow y) ∧
 (∀ j, (y j).val=AspisR1BatchedFoldSourceStep.sourcePush terms (x j).val
   ((powerLimb power j).val*basis.val)) ∧
 (∀ j, NBB_Phase.Bound (terms+1) (y j).val) := by
 obtain ⟨y,run,value⟩ := literal_row_refines_model x power basis terms hc hb hp
 refine ⟨y,run,value,?_⟩
 intro j
 rw [value]
 exact NBB_Phase.next terms (x j).val (powerLimb power j).val basis.val (hc j) hb (hp j)

/-- A phase-compatible row update has one complete result carrier. -/
theorem unique (x : Fin 4 → U64) (power : S7Kani2OwnedRow.K) (basis : U32)
 (terms : Nat) (a b : S7Kani2OwnedRow.Row)
 (ha : S7Kani2OwnedRow.residue_owned (makeRow x) power basis (decide (terms%4=3))=ok a)
 (hb : S7Kani2OwnedRow.residue_owned (makeRow x) power basis (decide (terms%4=3))=ok b) : a=b := by
 exact Result.ok.inj (ha.symm.trans hb)
#print axioms source
#print axioms unique
end NBB_Row
