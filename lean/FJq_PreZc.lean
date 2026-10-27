import FJq_ChallengeZc
import R3SemanticRemainingJoins
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_PreZc
open Aeneas Aeneas.Std AspisR1PublicPreparation
open FIz_ConcretePack (embed)
theorem value (c : r1_wire.Challenges) (alpha : Array aspis_core.field.QM31 10#usize)
    (v : LiteralOpeningView.View)
    (same : v.semantic.map Prod.snd=FJq_ChallengeSlots.values c alpha) :
    R0P.SemSource.preZc (fun j=>(v.semantic.map Prod.snd).getD j.val 0)=
      fun i=>embed (FJn_MainPoint.point c.zc i) := by
  funext i
  change (v.semantic.map Prod.snd).getD (3+i.val) 0=_
  rw [same]
  exact FJq_ChallengeZc.value c alpha i
#print axioms value
end AspisR1.FJq_PreZc
end
