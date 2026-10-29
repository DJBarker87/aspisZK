import R1Z.PV_RunJoin_R24Cell0_54
import R1Z.PV_RunJoin_R24Cell1_54
import R1Z.PV_RunJoin_R24Cell2_54
import R1Z.PV_RunJoin_R24Cell3_54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_R24Decompose54
abbrev Q := (U32 × U32) × (U32 × U32)
theorem complete (left right : Q) (u v : U64) :
  PV_RunJoin_CircleNeutralR24Tail53.tail left right u v = (do
    let x0 ← PV_RunJoin_R24Cell0_54.cell left right u v
    let x1 ← PV_RunJoin_R24Cell1_54.cell left right u v
    let x2 ← PV_RunJoin_R24Cell2_54.cell left right u v
    let x3 ← PV_RunJoin_R24Cell3_54.cell left right u v
    let c0 ← PV_RunJoin_CircleR72Raw52.field.CM31.new x0 x1
    let c1 ← PV_RunJoin_CircleR72Raw52.field.CM31.new x2 x3
    ok (some (c0,c1))) := by
  simp only [PV_RunJoin_CircleNeutralR24Tail53.tail,PV_RunJoin_R24Cell0_54.cell,PV_RunJoin_R24Cell1_54.cell,PV_RunJoin_R24Cell2_54.cell,PV_RunJoin_R24Cell3_54.cell,bind_assoc_eq,bind_tc_ok]
#print axioms complete
end R1Z.PV_RunJoin_R24Decompose54
