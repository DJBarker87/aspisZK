import R1Z.PV_RunJoin_CircleR72Op2252
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op23 (self : Q) :
    AspisR72Sampler.field.QM31.try_inv (encQ self) = (do let x ← PV_RunJoin_CircleR72Raw52.field.QM31.try_inv self; ok ((Option.map encQ) x)) := by
  unfold AspisR72Sampler.field.QM31.try_inv PV_RunJoin_CircleR72Raw52.field.QM31.try_inv
  simp only [op2,op7,op16,op19,op20,op21,op22,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op23
end R1Z.PV_RunJoin_CircleR72Ops52
