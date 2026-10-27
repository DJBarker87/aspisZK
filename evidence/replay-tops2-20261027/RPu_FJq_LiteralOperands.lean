import RPu_FJq_ChallengeLambda
import RPu_FJq_ChallengeChi
import RPu_FJq_ChallengeTheta
import RPu_FJq_ChallengeMu
import RPu_FJq_ChallengeEta
import RPu_FJq_PreZc
import RPu_FJq_ChallengeAlpha
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_LiteralOperands
open Aeneas Aeneas.Std AspisR1PublicPreparation
open FIz_ConcretePack (embed)
def challenge (v : LiteralOpeningView.View) (n : Nat) := (v.semantic.map Prod.snd).getD n 0
/-- Every literal challenge argument is the exact same source scalar/array. -/
theorem value (c : r1_wire.Challenges) (alpha : Array aspis_core.field.QM31 10#usize)
    (v : LiteralOpeningView.View)
    (same : v.semantic.map Prod.snd=FJq_ChallengeSlots.values c alpha) :
    challenge v 0=embed (FIp_SemanticValues.decode c.lambda) ∧
    challenge v 1=embed (FIp_SemanticValues.decode c.chi) ∧
    challenge v 2=embed (FIp_SemanticValues.decode c.theta) ∧
    challenge v 13=embed (FIp_SemanticValues.decode c.mu) ∧
    challenge v 14=embed (FIp_SemanticValues.decode c.eta) ∧
    R0P.SemSource.preZc (fun j=>challenge v j.val)=(fun i=>embed (FJn_MainPoint.point c.zc i)) ∧
    (fun i : Fin 10=>challenge v (15+i.val))=(fun i=>embed (FJn_MainPoint.point alpha i)) := by
  refine ⟨?_,?_,?_,?_,?_,FJq_PreZc.value c alpha v same,?_⟩
  · unfold challenge;rw [same];exact FJq_ChallengeLambda.value c alpha
  · unfold challenge;rw [same];exact FJq_ChallengeChi.value c alpha
  · unfold challenge;rw [same];exact FJq_ChallengeTheta.value c alpha
  · unfold challenge;rw [same];exact FJq_ChallengeMu.value c alpha
  · unfold challenge;rw [same];exact FJq_ChallengeEta.value c alpha
  · funext i;unfold challenge;rw [same];exact FJq_ChallengeAlpha.value c alpha i
#print axioms value
end AspisR1.FJq_LiteralOperands
end
