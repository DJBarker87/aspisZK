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
  rw [op2]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro zero _
  cases zero with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true,if_false]
    simp only [q_c0,q_c1,op19,op7,op22,op16,op20,op21,
      bind_assoc_eq,bind_tc_ok,Option.map_some]
    all_goals simp only [encQ]
    all_goals rfl

#print axioms op23
end R1Z.PV_RunJoin_CircleR72Ops52
