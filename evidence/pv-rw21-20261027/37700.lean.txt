import R1Z.ProverRw19P6RawContextIdentity
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21Op223Source
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

/-- Retained initializer/iterator/inline-loop semantics, not a new extraction
of the shipped whole helper. The shipped-to-reference frontier stays explicit. -/
def extracted (ops : ExternalFuns) := @ProverRw19P6RawContextIdentity.context _ ops

theorem reference (ops : ExternalFuns) :
    extracted ops = @ProverRwP6CompressSource.compress _ ops :=
  (ProverRw19P6RawContextIdentity.identity ops).symm

theorem row (ops : ExternalFuns) (tag : U32) (values : Slice U32)
    (lambda : aspis_core.field.QM31) :
    extracted ops tag values lambda =
      @ProverRwP6CompressSource.compress _ ops tag values lambda := by
  rw [reference]

-- This is a criterion, not a discharge: no installed dictionary is substituted
-- for the original caller to make the missing source law true by definition.
theorem source_iff (ops primitives : ExternalFuns) :
    ops.op223 = extracted primitives ↔
    ops.op223 = @ProverRwP6CompressSource.compress _ primitives := by
  rw [reference]

#print axioms extracted
#print axioms reference
#print axioms row
#print axioms source_iff
end R1Z.ProverRw21Op223Source
