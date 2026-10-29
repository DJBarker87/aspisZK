import R1Z.PV_RunJoin_CircleR72Op2652
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op27 (c : Unit) (tupled_args : Std.U64) :
    AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call c tupled_args = PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call c tupled_args := by
  unfold AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call
  simp only [op3,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals rfl

#print axioms op27
end R1Z.PV_RunJoin_CircleR72Ops52
