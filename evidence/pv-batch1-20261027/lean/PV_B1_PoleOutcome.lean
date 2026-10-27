import PV_B1_PoleBridge
import PV_B1_Orig258_Op258FoldAll
set_option autoImplicit false
noncomputable section
namespace PV_B1_PoleOutcome
open Aeneas Aeneas.Std Result PV_B1_258 PV_B1_PoleBody

theorem total (values : Rows) (masks : Array U16 64#usize) (chi : Q)
    (bound : values.val.length≤1024) : ∃ b, all_slots_clear values masks chi=ok b := by
  rw [PV_B1_PoleBridge.op258_source]
  exact PV_B1_Orig258_Op258Total.source_total values masks chi bound

theorem oversized (values : Rows) (masks : Array U16 64#usize) (chi : Q)
    (bound : 1024<values.val.length) : all_slots_clear values masks chi=fail .arrayOutOfBounds := by
  rw [PV_B1_PoleBridge.op258_source]
  exact PV_B1_Orig258_Op258Outside.source_failure values masks chi bound

theorem classified (values : Rows) (masks : Array U16 64#usize) (chi : Q) :
    (values.val.length≤1024 ∧ ∃ b, all_slots_clear values masks chi=ok b) ∨
    (1024<values.val.length ∧ all_slots_clear values masks chi=fail .arrayOutOfBounds) := by
  by_cases h : values.val.length≤1024
  · exact Or.inl ⟨h,total values masks chi h⟩
  · exact Or.inr ⟨by omega,oversized values masks chi (by omega)⟩

theorem never_diverges (values : Rows) (masks : Array U16 64#usize) (chi : Q) :
    all_slots_clear values masks chi≠div := by
  rcases classified values masks chi with ⟨_,b,hb⟩ | ⟨_,hf⟩
  · rw [hb]; intro h; cases h
  · rw [hf]; intro h; cases h

theorem failure_iff (values : Rows) (masks : Array U16 64#usize) (chi : Q) :
    all_slots_clear values masks chi=fail .arrayOutOfBounds ↔ 1024<values.val.length := by
  constructor
  · intro hf
    rcases classified values masks chi with ⟨_,b,hb⟩ | ⟨h,_⟩
    · rw [hb] at hf; cases hf
    · exact h
  · exact oversized values masks chi

theorem false_still_fails (values : Rows) (masks : Array U16 64#usize) (chi : Q)
    (bound : 1024<values.val.length) :
    all_slots_clear_loop0 values masks chi false 0#usize=fail .arrayOutOfBounds := by
  rw [PV_B1_PoleBridge.loop_result]
  exact PV_B1_Orig258_Op258Outside.loop_failure values masks chi bound 0#usize false
    (by change 0≤1024; omega)

theorem truth_iff (values : Rows) (masks : Array U16 64#usize) (chi : Q) :
    all_slots_clear values masks chi=ok true ↔
      values.val.length≤1024 ∧ ∀ i : Nat, i<values.val.length →
        PV_B1_Orig258_Op258Fold.keep values masks chi
          (PV_B1_Orig258_PoleAdvance.advance i 0#usize)=true := by
  rw [PV_B1_PoleBridge.op258_source]
  exact PV_B1_Orig258_Op258FoldAll.all_inputs values masks chi

-- This concerns the modeled bounds failure, not native OS failures.
theorem failure_same_length (a b : Rows) (ma mb : Array U16 64#usize) (ca cb : Q)
    (hlen : a.val.length=b.val.length) :
    all_slots_clear a ma ca=fail .arrayOutOfBounds ↔ all_slots_clear b mb cb=fail .arrayOutOfBounds := by
  rw [failure_iff,failure_iff,hlen]
#print axioms total
#print axioms oversized
#print axioms classified
#print axioms never_diverges
#print axioms failure_iff
#print axioms false_still_fails
#print axioms truth_iff
#print axioms failure_same_length
end PV_B1_PoleOutcome
