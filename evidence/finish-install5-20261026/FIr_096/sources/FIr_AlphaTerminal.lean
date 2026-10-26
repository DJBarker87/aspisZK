import FIr_AcceptedTerminal
import FIr_AlphaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_AlphaTerminal
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation

theorem reached {H : Type} (B : FinishModel.Boundaries)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : FIr_AcceptedTerminal.MainPub) (bytes : Slice U8) (hash : H)
    (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (success : AspisR1CurrentCaller.S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
      (FIq_Terminal.install B) D pub bytes hash=ok (.Ok sem)) :
    ∃ (challenges : r1_wire.Challenges) (terminal : aspis_core.field.QM31),
      FIq_Terminal.terminal (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub)
        (retainedSem sem).claims (retainedSem sem).alpha challenges=ok (.Ok terminal) ∧
      (∀ q∈(retainedSem sem).alpha.val,FIp_SemanticValues.Canon q) := by
  obtain ⟨pre,before,after,challenges,running,terminal,mask16,mask10,claim0,claim27,mask,etaTerminal,masked,extra28,
    parsed,rounds,called,rest⟩ := FIr_AcceptedTerminal.verified B D pub bytes hash sem success
  exact ⟨challenges,terminal,called,FIr_AlphaCanonical.verified (FIq_Terminal.install B) D pub bytes hash sem success⟩

#print axioms reached
end AspisR1.FIr_AlphaTerminal
end
