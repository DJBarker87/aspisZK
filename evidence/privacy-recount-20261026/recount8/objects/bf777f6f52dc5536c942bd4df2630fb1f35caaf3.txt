import R1Z.PV_CB_Op105Exact
import R1Z.ProverRwP7CurrentBaseBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_InvLoop
open Aeneas Aeneas.Std Result ControlFlow
namespace S
abbrev mul := PV_CB_ShippedOp105.aspis_core.field.M31.mul
abbrev body := PV_CB_ShippedOp105.aspis_core.field.M31.pow_loop.body
abbrev run := PV_CB_ShippedOp105.aspis_core.field.M31.pow_loop
abbrev pow := PV_CB_ShippedOp105.aspis_core.field.M31.pow
abbrev inv := PV_CB_ShippedOp105.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv
end S
namespace R
abbrev mul := ProverRwSuccessInverseSource.field.M31.mul
abbrev body := ProverRwSuccessInverseSource.field.M31.pow_loop.body
abbrev run := ProverRwSuccessInverseSource.field.M31.pow_loop
abbrev pow := ProverRwSuccessInverseSource.field.M31.pow
abbrev inv := ProverRwSuccessInverseSource.field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv
end R
/-- Compare the symbolic primitive before transporting the loop functional. -/
theorem mul (a b : U32) : S.mul a b = R.mul a b := by
  refine Eq.trans ?_ (ProverRwP7CurrentBaseBridge.mul a b)
  unfold S.mul ProverRwP7CurrentBaseBridge.S.mul
    PV_CB_ShippedOp105.aspis_core.field.M31.mul
    ProverRwP7CurrentFieldSource.aspis_core.field.M31.mul
    PV_CB_ShippedOp105.aspis_core.field.reduce_u64
    ProverRwP7CurrentFieldSource.aspis_core.field.reduce_u64
    PV_CB_ShippedOp105.aspis_core.field.ct.reduce64
    ProverRwP7CurrentFieldSource.aspis_core.field.ct.reduce64
    PV_CB_ShippedOp105.aspis_core.field.ct.subtract_p
    ProverRwP7CurrentFieldSource.aspis_core.field.ct.subtract_p
    PV_CB_ShippedOp105.aspis_core.field.P
    ProverRwP7CurrentFieldSource.aspis_core.field.P
  rfl

theorem body (exp : U64) (base acc : U32) : S.body exp base acc = R.body exp base acc := by
  simp only [S.body,R.body,
    PV_CB_ShippedOp105.aspis_core.field.M31.pow_loop.body,
    ProverRwSuccessInverseSource.field.M31.pow_loop.body,mul]
/-- The loop stays symbolic for arbitrary exponent; no recurrence evaluation. -/
theorem run (exp : U64) (base acc : U32) : S.run exp base acc = R.run exp base acc := by
  unfold S.run R.run PV_CB_ShippedOp105.aspis_core.field.M31.pow_loop
    ProverRwSuccessInverseSource.field.M31.pow_loop
  apply congrArg (fun f => loop f (exp,base,acc))
  funext triple
  rcases triple with ⟨e,b,a⟩
  exact body e b a

theorem pow (x : U32) (exp : U64) : S.pow x exp = R.pow x exp := by
  simp only [S.pow,R.pow,PV_CB_ShippedOp105.aspis_core.field.M31.pow,
    ProverRwSuccessInverseSource.field.M31.pow,
    PV_CB_ShippedOp105.aspis_core.field.M31.ONE,
    ProverRwSuccessInverseSource.field.M31.ONE,AspisR1ProducerRelease47.field.M31.ONE,run]

#print axioms mul
#print axioms body
#print axioms run
#print axioms pow
end R1Z.PV_Join_InvLoop
