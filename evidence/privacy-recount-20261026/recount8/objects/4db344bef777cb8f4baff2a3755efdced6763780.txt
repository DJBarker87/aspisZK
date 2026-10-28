import R1Z.PV_Join_ProducerCanonical5
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_CanonicalPrimitives5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5
variable [ExternalTypes]
/-- A local loop interface; its concrete caller instance is proved below. -/
structure Laws (dict : ExternalFuns) : Prop where
  add : ∀ x y, Q x → Q y → ∃ z, dict.op67 x y = .ok z ∧ Q z
  scale : ∀ x s, ∃ z, dict.op70 x s = .ok z ∧ Q z
  zero : dict.op64 = .ok ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩

theorem caller (base : ExternalTypes) (ops : @ExternalFuns (PV_Join_PublicCaller.native base)) :
    @Laws (PV_Join_PublicCaller.native base) (PV_Join_PublicCaller.selected base ops) := by
  refine @Laws.mk (PV_Join_PublicCaller.native base) (PV_Join_PublicCaller.selected base ops) ?_ ?_ ?_
  · exact PV_Join_ProducerCanonical5.add base ops
  · exact PV_Join_ProducerCanonical5.scale base ops
  · change Result.ok (ProverRwDictionaryTower.fromQ AspisR1ProducerRelease47.field.QM31.ZERO) = _
    rw [AspisR1ProducerRelease47.field.QM31.ZERO]
    rfl

#print axioms caller
end R1Z.PV_Join_CanonicalPrimitives5
