import R1Z.PV_RunJoin_CircleNeutralR24Split53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralR24Prefix53
abbrev Q := (U32 × U32) × (U32 × U32)
open PV_RunJoin_CircleNeutralShape53

theorem complete (left right : Q) (hl : QC left) (hr : QC right) :
    PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul left right =
      PV_RunJoin_CircleNeutralR24Tail53.tail left right
        (PV_RunJoin_CircleNeutralR24Word53.word (AspisV8R19.PartialProduct.foldOnce
          (left.2.1.val*right.2.1.val+4611686014132420609-left.2.2.val*right.2.2.val)))
        (PV_RunJoin_CircleNeutralR24Word53.word (AspisV8R19.PartialProduct.foldOnce
          (left.2.1.val*right.2.2.val+left.2.2.val*right.2.1.val))) := by
  rw [PV_RunJoin_CircleNeutralR24Body53.canonical left right hl hr,
    PV_RunJoin_CircleNeutralR24Split53.body]
  rw [PV_RunJoin_CircleNeutralR24U53.complete _ _ _ _ hl.2.1 hl.2.2 hr.2.1 hr.2.2,bind_tc_ok,
    PV_RunJoin_CircleNeutralR24V53.complete _ _ _ _ hl.2.1 hl.2.2 hr.2.1 hr.2.2,bind_tc_ok]

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralR24Prefix53
