import FJn_MainTerminal
import FJn_AcceptedChallenges
import FJa_ClaimsOnRun
import FIr_AlphaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_AcceptedTerminalValue
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation
open FIz_ConcretePack (embed)
attribute [local irreducible] R0P.SemSource.terminalValue
  FJn_MainPoint.point FJn_MainClaims.claims FIw_PublicModel.ofPublic FJa_PublicCopy.native
/-- Same accepted source call supplies every scalar/claims/point canonicality.
Only the explicit public word bounds remain locally; literal-frame transport
is not asserted by this source-value theorem. -/
theorem value (std : ClaimsUnrolledFinish.StdCalls) (ops : Ops) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (bounds : FJa_PublicBounds.Bounds (FJa_PublicCopy.native (FirstComposition.toRetainedPublic pub)))
    (accepted : (AspisS1NativeBufferClaimTrace.semanticBase ops
      (ClaimsUnrolledFinish.install std (FIq_Terminal.install B))).op9 D pub bytes hash none=ok (.Ok sem)) :
    ∃ (c : AspisR1PublicPreparation.r1_wire.Challenges) (out : AspisR1PublicPreparation.aspis_core.field.QM31),
      FIq_Terminal.terminal (FirstComposition.toRetainedPublic pub)
        (retainedSem sem).claims (retainedSem sem).alpha c=ok (.Ok out) ∧
      FIp_SemanticValues.Canon out ∧ embed (FIp_SemanticValues.decode out)=
      R0P.SemSource.terminalValue
        (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic (FJa_PublicCopy.native (FirstComposition.toRetainedPublic pub))))
        (embed (FIp_SemanticValues.decode c.lambda)) (embed (FIp_SemanticValues.decode c.chi))
        (embed (FIp_SemanticValues.decode c.theta)) (embed (FIp_SemanticValues.decode c.mu))
        (fun i=>embed (FJn_MainPoint.point c.zc i)) ConcretePackBasis.basis
        (fun j l=>embed (FJn_MainClaims.claims (retainedSem sem).claims j l))
        (fun i=>embed (FJn_MainPoint.point (retainedSem sem).alpha i)) := by
  have source : S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
      (FIq_Terminal.install (ClaimsUnrolledFinish.install std B)) D pub bytes hash=ok (.Ok sem) := accepted
  obtain ⟨c,out,called,hl,hchi,ht,hm,he,hz⟩:=
    FJn_AcceptedChallenges.value (ClaimsUnrolledFinish.install std B) D pub bytes hash sem source
  have hc:=FJa_ClaimsOnRun.value std ops (FIq_Terminal.install B) D pub bytes hash sem accepted
  have ha:=FIr_AlphaCanonical.verified (FIq_Terminal.install (ClaimsUnrolledFinish.install std B)) D pub bytes hash sem source
  exact ⟨c,out,called,FJn_MainTerminal.value (FirstComposition.toRetainedPublic pub)
    (retainedSem sem).claims (retainedSem sem).alpha c out hc ha hz hl hchi ht hm bounds called⟩
#print axioms value
end AspisR1.FJn_AcceptedTerminalValue
end
