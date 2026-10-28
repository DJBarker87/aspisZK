import R1Z.PV_ProverRwP7CurrentComplexBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CurrentQuarticBridge
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev C := ProverRwFull.aspis_core.field.CM31
namespace S
abbrev add := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add
abbrev mul := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul
abbrev mul_by_r := ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r
end S

theorem mul_by_r (a : C) : S.mul_by_r a = mapResult fromC
    (AspisR1ProducerRelease47.field.mul_by_r (toC a)) := by
  simp only [S.mul_by_r,ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r,
    ProverRwP7CurrentBaseBridge.double,ProverRwP7CurrentBaseBridge.sub,
    ProverRwP7CurrentBaseBridge.add,AspisR1ProducerRelease47.field.mul_by_r,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,toC,fromC]

theorem add (a b : Q) : S.add a b = qAdd a b := by
  simp only [S.add,ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add,
    PV_ProverRwP7CurrentComplexBridge.add,qAdd,AspisR1ProducerRelease47.field.QM31.add,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,toQ,fromQ,toC,fromC]

theorem mul (a b : Q) : S.mul a b = qMul a b := by
  simp only [S.mul,ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul,
    PV_ProverRwP7CurrentComplexBridge.add,PV_ProverRwP7CurrentComplexBridge.sub,
    PV_ProverRwP7CurrentComplexBridge.mul,mul_by_r,qMul,
    AspisR1ProducerRelease47.field.QM31.mul,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,toQ,fromQ,toC,fromC]
#print axioms mul_by_r
#print axioms add
#print axioms mul
end R1Z.PV_CurrentQuarticBridge
