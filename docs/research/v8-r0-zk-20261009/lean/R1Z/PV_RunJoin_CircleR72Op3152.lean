import R1Z.PV_RunJoin_CircleR72Op3052
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op31 (self : Q) (rhs : Q) :
    AspisR72Sampler.field.QM31.mul (encQ self) (encQ rhs) = (do let x ← PV_RunJoin_CircleR72Raw52.field.QM31.mul self rhs; ok (encQ x)) := by
  unfold AspisR72Sampler.field.QM31.mul PV_RunJoin_CircleR72Raw52.field.QM31.mul
  rw [op30]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro fast _
  cases fast with
  | some q => rfl
  | none =>
    simp only [Option.map_none]
    simp only [q_c0,q_c1,op20,op24,op7,op22,bind_assoc_eq,bind_tc_ok]
    all_goals simp only [encQ]
    all_goals rfl

#print axioms op31
end R1Z.PV_RunJoin_CircleR72Ops52
