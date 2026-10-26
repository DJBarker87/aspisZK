import R1Z.PV_CB_CurrentComplexMore
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CurrentQuartic
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev C := ProverRwFull.aspis_core.field.CM31
abbrev Q := ProverRwFull.aspis_core.field.QM31
namespace S
abbrev r := ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r
abbrev add := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add
abbrev mul := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul
abbrev square := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square
abbrev scale := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31
end S
theorem r (a : C) : S.r a = mapResult fromC
    (AspisR1ProducerRelease47.field.mul_by_r (toC a)) := by
  simp only [S.r,ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r,
    ProverRwP7CurrentBaseBridge.double,ProverRwP7CurrentBaseBridge.sub,
    ProverRwP7CurrentBaseBridge.add,AspisR1ProducerRelease47.field.mul_by_r,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,toC,fromC]
theorem add (a b : Q) : S.add a b = mapResult fromQ
    (AspisR1ProducerRelease47.field.QM31.add (toQ a) (toQ b)) := by
  simp only [S.add,ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add,
    PV_CB_CurrentComplex.add,AspisR1ProducerRelease47.field.QM31.add,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,toQ,fromQ,toC,fromC]
theorem mul (a b : Q) : S.mul a b = mapResult fromQ
    (AspisR1ProducerRelease47.field.QM31.mul (toQ a) (toQ b)) := by
  simp only [S.mul,ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul,
    PV_CB_CurrentComplex.mul,PV_CB_CurrentComplex.add,PV_CB_CurrentComplex.sub,r,
    AspisR1ProducerRelease47.field.QM31.mul,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,toQ,fromQ,toC,fromC]
theorem square (a : Q) : S.square a = mapResult fromQ
    (AspisR1ProducerRelease47.field.QM31.square (toQ a)) := by
  simp only [S.square,ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square,
    PV_CB_CurrentComplexMore.square,PV_CB_CurrentComplexMore.double,
    PV_CB_CurrentComplex.mul,PV_CB_CurrentComplex.add,r,
    AspisR1ProducerRelease47.field.QM31.square,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,toQ,fromQ,toC,fromC]
theorem scale (a : Q) (b : U32) : S.scale a b = mapResult fromQ
    (AspisR1ProducerRelease47.field.QM31.mul_m31 (toQ a) b) := by
  simp only [S.scale,ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31,
    PV_CB_CurrentComplexMore.scale,AspisR1ProducerRelease47.field.QM31.mul_m31,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,toQ,fromQ,toC,fromC]
#print axioms r
#print axioms add
#print axioms mul
#print axioms square
#print axioms scale
end R1Z.PV_CB_CurrentQuartic
