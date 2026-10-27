import R1Z.ProverRwP6CompressSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CompressSupport
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev M := aspis_core.field.M31
abbrev Q := aspis_core.field.QM31
/-- Exact callback support of the extracted compressor, including all Result
    failures and divergence; no totality or algebraic premise is required. -/
theorem congr (left right : ExternalFuns)
    (from_m31 : left.op61 = right.op61)
    (from_cm31 : left.op66 = right.op66)
    (add : left.op67 = right.op67)
    (mul : left.op69 = right.op69)
    (scale : left.op70 = right.op70)
    (tag : M) (values : Slice M) (lambda : Q) :
    @ProverRwP6CompressSource.compress _ left tag values lambda =
    @ProverRwP6CompressSource.compress _ right tag values lambda := by
  simp only [ProverRwP6CompressSource.compress,
    ProverRwP6CompressSource.compress_loop,
    ProverRwP6CompressSource.compress_loop.body,
    aspis_core.field.CM31.from_m31, aspis_core.field.QM31.from_cm31,
    aspis_core.field.QM31.add, aspis_core.field.QM31.mul,
    aspis_core.field.QM31.mul_m31,from_m31,from_cm31,add,mul,scale]
#print axioms congr
end R1Z.PV_CB_CompressSupport
