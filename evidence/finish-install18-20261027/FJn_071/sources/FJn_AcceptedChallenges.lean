import FJn_BeginCanonical
import FIr_AcceptedTerminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_AcceptedChallenges
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation
/-- The accepted terminal and canonical challenges come from ONE verify_roots
inversion, so there is no independent successful begin or terminal witness. -/
theorem value {H : Type} (B : FinishModel.Boundaries)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : FIr_AcceptedTerminal.MainPub) (bytes : Slice U8) (hash : H)
    (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (success : AspisR1CurrentCaller.S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
      (FIq_Terminal.install B) D pub bytes hash=ok (.Ok sem)) :
    ∃ (c : r1_wire.Challenges) (out : aspis_core.field.QM31),
      FIq_Terminal.terminal (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub)
        (retainedSem sem).claims (retainedSem sem).alpha c=ok (.Ok out) ∧
      FIp_SemanticValues.Canon c.lambda ∧ FIp_SemanticValues.Canon c.chi ∧
      FIp_SemanticValues.Canon c.theta ∧ FIp_SemanticValues.Canon c.mu ∧
      FIp_SemanticValues.Canon c.eta ∧ ∀ x∈c.zc.val,FIp_SemanticValues.Canon x := by
  obtain ⟨pre,initial,before,c,payload,root,parsed,publicInit,begin,finish,rest⟩:=
    AspisR1CurrentCaller.S1SemanticInstallation.verify_roots AspisS1ExtractedRoundChildren.children
      (FIq_Terminal.install B) D pub bytes hash sem success
  obtain ⟨running,after,out,m16,m10,row0,q27,mask,prod,sum,extra,
    rounds,called,rest⟩:=FIr_FinishComparison.terminal_comparison_of_finish_success AspisS1ExtractedRoundChildren.children
      (S1SemanticRootCopy.install (FIq_Terminal.install B)) (retainedDigest D)
      (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub) pre before c none (retainedSem sem) finish
  exact ⟨c,out,called,FJn_BeginCanonical.value (retainedDigest D) pre initial before c begin⟩
#print axioms value
end AspisR1.FJn_AcceptedChallenges
end
