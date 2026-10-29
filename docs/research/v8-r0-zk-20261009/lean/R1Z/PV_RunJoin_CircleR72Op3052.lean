import R1Z.PV_RunJoin_CircleR72Op2952
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op30 (left : Q) (right : Q) :
    AspisR72Sampler.field.r24_canonical_mul (encQ left) (encQ right) = (do let x ← PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul left right; ok ((Option.map encQ) x)) := by
  unfold AspisR72Sampler.field.r24_canonical_mul PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul
  simp only [q_c0,q_c1,cm_a,cm_b,op3]
  split_ifs
  all_goals
    repeat' (first
      | rw [op27]
      | rw [op28]
      | rw [op29]
      | rw [bind_assoc_eq]
      | rw [bind_tc_ok]
      | (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro value reachable))
  all_goals simp only [Option.map_none,Option.map_some,encQ,encCM]
  all_goals rfl

#print axioms op30
end R1Z.PV_RunJoin_CircleR72Ops52
