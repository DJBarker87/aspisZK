import R1Z.PV_CB3_Op258Total
import R1Z.PV_CB3_Op258Outside
import R1Z.PV_CB3_Op258Staged
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_Op258Outcome
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
abbrev Rows := Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize)

theorem classified (values : Rows) (masks : Array U16 64#usize) (chi : aspis_core.field.QM31) :
    (values.val.length ≤ 1024 ∧ ∃ b,
      PV_CB3_Op258Ref.reference.all_slots_clear values masks chi = ok b) ∨
    (1024 < values.val.length ∧
      PV_CB3_Op258Ref.reference.all_slots_clear values masks chi = fail .arrayOutOfBounds) := by
  by_cases h : values.val.length ≤ 1024
  · exact Or.inl ⟨h,PV_CB3_Op258Total.source_total values masks chi h⟩
  · have hl : 1024 < values.val.length := by omega
    exact Or.inr ⟨hl,PV_CB3_Op258Outside.source_failure values masks chi hl⟩

theorem never_diverges (values : Rows) (masks : Array U16 64#usize) (chi : aspis_core.field.QM31) :
    PV_CB3_Op258Ref.reference.all_slots_clear values masks chi ≠ div := by
  rcases classified values masks chi with ⟨_,b,hb⟩ | ⟨_,hf⟩
  · rw [hb]; intro impossible; cases impossible
  · rw [hf]; intro impossible; cases impossible

theorem failure_iff (values : Rows) (masks : Array U16 64#usize) (chi : aspis_core.field.QM31) :
    PV_CB3_Op258Ref.reference.all_slots_clear values masks chi = fail .arrayOutOfBounds ↔
      1024 < values.val.length := by
  constructor
  · intro hf
    rcases classified values masks chi with ⟨_,b,hb⟩ | ⟨h,_⟩
    · rw [hb] at hf; cases hf
    · exact h
  · exact PV_CB3_Op258Outside.source_failure values masks chi

theorem success_iff (values : Rows) (masks : Array U16 64#usize) (chi : aspis_core.field.QM31) :
    (∃ b, PV_CB3_Op258Ref.reference.all_slots_clear values masks chi = ok b) ↔
      values.val.length ≤ 1024 := by
  constructor
  · rintro ⟨b,hb⟩
    rcases classified values masks chi with ⟨h,_⟩ | ⟨_,hf⟩
    · exact h
    · rw [hf] at hb; cases hb
  · exact PV_CB3_Op258Total.source_total values masks chi

/-- Complete Result classification of the prospective reference selection.
This is deliberately not named op258_source: native association remains open. -/
theorem selected [ExternalTypes] (ops : ExternalFuns) (values : Rows)
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31) :
    (PV_CB3_Op258Staged.selected ops).op258 values masks chi = fail .arrayOutOfBounds ↔
      1024 < values.val.length := failure_iff values masks chi
#print axioms classified
#print axioms never_diverges
#print axioms failure_iff
#print axioms success_iff
#print axioms selected
end R1Z.PV_CB3_Op258Outcome
