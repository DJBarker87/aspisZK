import R1Z.PV_CurrentQuarticBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CurrentScale
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev S := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul_m31
abbrev T := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31

theorem complex (a : C) (b : U32) : S a b = mapResult fromC
    (AspisR1ProducerRelease47.field.CM31.mul_m31 (toC a) b) := by
  simp only [S,ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul_m31,
    ProverRwP7CurrentBaseBridge.mul,AspisR1ProducerRelease47.field.CM31.mul_m31,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,toC,fromC]

theorem quartic (a : Q) (b : U32) : T a b = mapResult fromQ
    (AspisR1ProducerRelease47.field.QM31.mul_m31 (toQ a) b) := by
  simp only [T,ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31,
    complex,AspisR1ProducerRelease47.field.QM31.mul_m31,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,toQ,fromQ,toC,fromC]
#print axioms complex
#print axioms quartic
end R1Z.PV_CurrentScale
