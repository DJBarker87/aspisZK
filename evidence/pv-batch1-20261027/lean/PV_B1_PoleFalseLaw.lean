import PV_B1_PoleOutcome
set_option autoImplicit false
noncomputable section
namespace PV_B1_PoleFalseLaw
open Aeneas Aeneas.Std Result PV_B1_Transport
open PV_B1_258 PV_B1_PoleBody
theorem false_iff (v : Rows) (m : Array U16 64#usize) (c : Q) :
    all_slots_clear v m c=ok false ↔ v.val.length≤1024 ∧
      ¬ (∀ i : Nat, i<v.val.length → PV_B1_Orig258_Op258Fold.keep v m c
        (PV_B1_Orig258_PoleAdvance.advance i 0#usize)=true) := by
  constructor
  · intro hf
    rcases PV_B1_PoleOutcome.classified v m c with ⟨bound,b,hb⟩ | ⟨_,he⟩
    · refine ⟨bound,?_⟩
      intro all
      have ht := (PV_B1_PoleOutcome.truth_iff v m c).mpr ⟨bound,all⟩
      rw [hf] at ht
      cases ht
    · rw [hf] at he; cases he
  · rintro ⟨bound,notall⟩
    obtain ⟨b,hb⟩ := PV_B1_PoleOutcome.total v m c bound
    cases b with
    | false => exact hb
    | true => exact False.elim (notall ((PV_B1_PoleOutcome.truth_iff v m c).mp hb).2)
#print axioms false_iff
end PV_B1_PoleFalseLaw
