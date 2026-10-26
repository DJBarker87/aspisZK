import R1Z.PV_CB_CurrentComplex
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CurrentComplexMore
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev C := ProverRwFull.aspis_core.field.CM31
namespace S
abbrev square := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.square
abbrev scale := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul_m31
abbrev double := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.double
end S
theorem square (a : C) : S.square a = mapResult fromC
    (AspisR1ProducerRelease47.field.CM31.square (toC a)) := by
  simp only [S.square,ProverRwP7CurrentFieldSource.aspis_core.field.CM31.square,
    ProverRwP7CurrentBaseBridge.mreduce,ProverRwP7CurrentBaseBridge.mul,
    ProverRwP7CurrentBaseBridge.double,AspisR1ProducerRelease47.field.CM31.square,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,toC,fromC,lift,
    ProverRwP7CurrentFieldSource.aspis_core.field.P,
    AspisR1ProducerRelease47.field.P]
theorem scale (a : C) (b : U32) : S.scale a b = mapResult fromC
    (AspisR1ProducerRelease47.field.CM31.mul_m31 (toC a) b) := by
  simp only [S.scale,ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul_m31,
    ProverRwP7CurrentBaseBridge.mul,AspisR1ProducerRelease47.field.CM31.mul_m31,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,toC,fromC]
theorem double (a : C) : S.double a = mapResult fromC
    (AspisR1ProducerRelease47.field.CM31.double (toC a)) := by
  exact PV_CB_CurrentComplex.add a a
#print axioms square
#print axioms scale
#print axioms double
end R1Z.PV_CB_CurrentComplexMore
