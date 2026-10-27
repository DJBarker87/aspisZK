import R1Z.PV_Join_InvLoop
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_InvSource
open Aeneas Aeneas.Std Result
/-- Transport the fixed-exponent inverse through the symbolic loop theorem. -/
theorem inverse (x : U32) : PV_Join_InvLoop.S.inv x = PV_Join_InvLoop.R.inv x := by
  simp only [PV_Join_InvLoop.S.inv,PV_Join_InvLoop.R.inv,
    PV_CB_ShippedOp105.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv,
    ProverRwSuccessInverseSource.field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv,
    PV_CB_ShippedOp105.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
    ProverRwSuccessInverseSource.field.M31.Insts.CoreCmpPartialEqM31.eq,
    ProverRwDictionaryDerived.mEq,
    ProverRwDictionaryDerivedSource.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
    PV_CB_ShippedOp105.aspis_core.field.M31.ZERO,
    ProverRwSuccessInverseSource.field.M31.ZERO,AspisR1ProducerRelease47.field.M31.ZERO,
    PV_CB_ShippedOp105.aspis_core.field.P,
    ProverRwSuccessInverseSource.field.P,AspisR1ProducerRelease47.field.P,
    PV_Join_InvLoop.pow]
#print axioms inverse
end R1Z.PV_Join_InvSource
