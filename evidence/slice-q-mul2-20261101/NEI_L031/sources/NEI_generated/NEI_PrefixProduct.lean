import NEI_FieldScalar
import NEI_PrefixWindows
set_option autoImplicit false
noncomputable section
namespace NEI_PrefixProduct
open Aeneas Aeneas.Std Result AspisR1

/-- The actual frozen emitted M31 body and prefix's same callee return the
same exact natural value, on every machine-word input. -/
theorem actual (lhs rhs : U32) :
    ∃ reply, NEI_LineFull.aspis_core.field.M31.mul lhs rhs = ok reply ∧
      NEG_PrefixFull.aspis_core.field.M31.mul lhs rhs = ok reply ∧
      reply.val = (lhs.val * rhs.val) % 2147483647 ∧ reply.val < 2147483647 := by
  obtain ⟨reply,run,value,canonical⟩ := NEG_PrefixStep.multiply lhs rhs
  have current : AspisR1CurrentWide.field.M31.mul lhs rhs = ok reply := by
    rw [AspisR1CurrentWide.Proof.m31_mul_same]
    exact run
  exact ⟨reply,(NEI_FieldScalar.m_mul lhs rhs).trans current,run,value,canonical⟩

/-- Primitive specialization only; no native loop or append result is assumed. -/
theorem specialize (lhs rhs : U32) (P : U32 → Prop)
    (universal : ∀ reply, reply.val < 2147483647 → P reply) :
    ∃ reply, NEI_LineFull.aspis_core.field.M31.mul lhs rhs = ok reply ∧
      NEG_PrefixFull.aspis_core.field.M31.mul lhs rhs = ok reply ∧ P reply := by
  obtain ⟨reply,actualRun,cohortRun,value,canonical⟩ := actual lhs rhs
  exact ⟨reply,actualRun,cohortRun,universal reply canonical⟩

#print axioms actual
#print axioms specialize
end NEI_PrefixProduct
end
