import R1Z.PV_RW_CompressBound
import R1Z.PV_CompressArity
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressReference
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6CompressControl
variable [ExternalTypes] [ExternalFuns]

-- Native step association is external evidence, never a Lean axiom. This
-- model theorem composes the proved step semantics with the extracted owner.
def sourceModel (tag : M) (values : Slice M) (lambda : Q) : Result Q := do
  let c ← aspis_core.field.CM31.from_m31 tag
  let out ← aspis_core.field.QM31.from_cm31 c
  let state ← PV_RW_CompressStep.run (PV_RW_CompressStep.shipped lambda) values.val (out,lambda)
  ok state.1

theorem reference (tag : M) (values : Slice M) (lambda : Q) :
    sourceModel tag values lambda = ProverRwP6CompressSource.compress tag values lambda := by
  rw [PV_CompressModel.compress]
  unfold sourceModel
  repeat' first | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro _ _
  rw [PV_RW_CompressStep.shipped_fold]
  rfl

def boundedModel (tag : M) (values : Slice M) (lambda : Q) : Result Q := do
  let c ← aspis_core.field.CM31.from_m31 tag
  let out ← aspis_core.field.QM31.from_cm31 c
  let state ← PV_RW_CompressBound.bounded (PV_RW_CompressStep.shipped lambda) 17 values.val (out,lambda)
  ok state.1

theorem arity16 (tag : M) (values : Array M 16#usize) (lambda : Q) :
    boundedModel tag (Array.to_slice values) lambda =
      ProverRwP6CompressSource.compress tag (Array.to_slice values) lambda := by
  rw [← reference]
  unfold boundedModel sourceModel
  repeat' first | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro _ _
  rw [PV_RW_CompressBound.sufficient _ _ _ (by
    have shape := PV_CompressArity.values_length values
    omega)]
#print axioms reference
#print axioms arity16
end R1Z.PV_RW_CompressReference
