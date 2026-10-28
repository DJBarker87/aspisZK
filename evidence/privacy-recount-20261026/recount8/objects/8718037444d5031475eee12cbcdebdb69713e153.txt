import R1Z.ProverRwP7CurrentBaseBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_ProverRwP7CurrentComplexBridge
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev C := ProverRwFull.aspis_core.field.CM31
namespace S
abbrev add := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.add
abbrev sub := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.sub
abbrev mul := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul
end S

theorem add (a b : C) : S.add a b = mapResult fromC
    (AspisR1ProducerRelease47.field.CM31.add (toC a) (toC b)) := by
  simp only [S.add,ProverRwP7CurrentFieldSource.aspis_core.field.CM31.add,
    ProverRwP7CurrentBaseBridge.add,AspisR1ProducerRelease47.field.CM31.add,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,toC,fromC]

theorem sub (a b : C) : S.sub a b = mapResult fromC
    (AspisR1ProducerRelease47.field.CM31.sub (toC a) (toC b)) := by
  simp only [S.sub,ProverRwP7CurrentFieldSource.aspis_core.field.CM31.sub,
    ProverRwP7CurrentBaseBridge.sub,AspisR1ProducerRelease47.field.CM31.sub,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,toC,fromC]

theorem mul (a b : C) : S.mul a b = mapResult fromC
    (AspisR1ProducerRelease47.field.CM31.mul (toC a) (toC b)) := by
  simp only [S.mul,ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul,
    ProverRwP7CurrentBaseBridge.mul,ProverRwP7CurrentBaseBridge.mreduce,
    ProverRwP7CurrentBaseBridge.sub,AspisR1ProducerRelease47.field.CM31.mul,
    mapResult_bind,bind_assoc_eq,bind_tc_ok,toC,fromC,lift]
theorem double (a : C) :
    ProverRwP7CurrentFieldSource.aspis_core.field.CM31.double a = mapResult fromC
      (AspisR1ProducerRelease47.field.CM31.add (toC a) (toC a)) := by
  exact add a a
#print axioms double
#print axioms add
#print axioms sub
#print axioms mul
end R1Z.PV_ProverRwP7CurrentComplexBridge
