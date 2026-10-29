import R1Z.PV_RunJoin_CircleNeutralR24Body53
import R1Z.PV_RunJoin_CircleNeutralR24Tail53
import R1Z.PV_RunJoin_CircleNeutralR24U53
import R1Z.PV_RunJoin_CircleNeutralR24V53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralR24Split53
abbrev Q := (U32 × U32) × (U32 × U32)
attribute [local irreducible] PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64
attribute [local irreducible] PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call

theorem body (left right : Q) : PV_RunJoin_CircleNeutralR24Body53.body left right = (do
    let u ← PV_RunJoin_CircleNeutralR24U53.source left.2.1 left.2.2 right.2.1 right.2.2
    let v ← PV_RunJoin_CircleNeutralR24V53.source left.2.1 left.2.2 right.2.1 right.2.2
    PV_RunJoin_CircleNeutralR24Tail53.tail left right u v) := by
  unfold PV_RunJoin_CircleNeutralR24Body53.body PV_RunJoin_CircleNeutralR24U53.source
    PV_RunJoin_CircleNeutralR24V53.source PV_RunJoin_CircleNeutralR24Tail53.tail
  simp only [lift,bind_tc_ok,PV_RunJoin_CircleNeutralR24Leaf53.pp,bind_assoc_eq]
  rfl

#print axioms body
end R1Z.PV_RunJoin_CircleNeutralR24Split53
