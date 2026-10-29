import R1Z.PV_RunJoin_R24Equation1_54
import R1Z.PV_RunJoin_R24PartialValues54
import R1Z.PV_RunJoin_R24NatBounds54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_R24Value1_54
open PV_RunJoin_NeutralValue54 PV_RunJoin_NeutralTowerValue54 PV_RunJoin_CircleNeutralShape53
open PV_RunJoin_R24Inputs54 PV_RunJoin_R24PartialValues54

theorem complete (a b : PV_RunJoin_NeutralTowerValue54.Q) (ha : QC a) (hb : QC b) :
    (PV_RunJoin_R24Equation1_54.accumulator a b (u a b) (v a b) : M)=
      (qm (qv a) (qv b)).1.2 := by
  unfold PV_RunJoin_R24Equation1_54.accumulator
  simp only [Nat.cast_add,Nat.cast_mul]
  rw [u_value a b ha hb,v_value a b]
  simp only [qm,qv,ca,cs,cm,cr,cv,scalar,Prod.fst,Prod.snd]
  ring
#print axioms complete
end R1Z.PV_RunJoin_R24Value1_54
