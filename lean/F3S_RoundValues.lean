import RowFinish_Control
import OraclePortCkptAbiTry
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_RoundValues
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
attribute [local instance] Classical.propDecidable
 theorem reached {W : Type} (ops : FinishOps W) (bytes : Slice U8) (alpha claim : E)
    (round : Usize) (value : E)
    (success : Port4D_Round.round (Port3_FinishStage.release ops) bytes alpha claim round=ok (.Ok value)) :
    ∃ r : RowFinish_Control.RoundValues ops bytes alpha claim,r.value=value := by
  unfold Port4D_Round.round at success
  obtain ⟨c0,h0,s0⟩ := OraclePortCkptAbiTry.bind_success _ _ _ success
  obtain ⟨c4,h4,s1⟩ := OraclePortCkptAbiTry.bind_success _ _ _ s0
  obtain ⟨lhs,ha,s2⟩ := OraclePortCkptAbiTry.bind_success _ _ _ s1
  obtain ⟨quarter,hq,s3⟩ := OraclePortCkptAbiTry.bind_success _ _ _ s2
  obtain ⟨rhs,hm,s4⟩ := OraclePortCkptAbiTry.bind_success _ _ _ s3
  simp only [Port3_FinishStage.release,Port3_FinishStage.ne,lift,bind_tc_ok] at s4
  by_cases equal : lhs=rhs
  · simp only [ne_eq,equal,not_true_eq_false,not_false_eq_true,decide_false,decide_true,
      Bool.false_eq_true,if_false,if_true] at s4
    obtain ⟨actual,he,returned⟩ := OraclePortCkptAbiTry.bind_success _ _ _ s4
    have same : actual=value := core.result.Result.Ok.inj (Result.ok.inj returned)
    exact ⟨⟨c0,c4,lhs,quarter,rhs,actual,h0,h4,ha,hq,hm,he⟩,same⟩
  · simp only [ne_eq,equal,not_true_eq_false,not_false_eq_true,decide_false,decide_true,
      Bool.false_eq_true,if_false,if_true] at s4
    cases s4
#print axioms reached
end AspisR1.F3S_RoundValues
end
