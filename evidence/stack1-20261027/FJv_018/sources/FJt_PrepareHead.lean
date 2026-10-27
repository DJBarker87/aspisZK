import F3U_PrepareHead
import SdkD_PrepareSource
import AuS1_Recovery
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_PrepareHead
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation.PreparedHashCode

theorem value (ops : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (accepted : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
      D pub proof hash none input=ok (.Ok p,scratch)) :
    ∃ (encoded : alloc.vec.Vec U8) (root state : State),
      AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (FirstComposition.toRetainedPublic pub)=ok (.Ok encoded) ∧
      (AuS1_Recovery.log ops B std D pub proof hash input).head?=
        some (PublicInitFrame.frame (AspisR1PublicPreparation.SourceDigestAddresses.rawBytes encoded.deref) root,state) := by
  have source := (SdkD_PrepareSource.source ops B std D pub proof hash input).trans accepted
  exact F3U_PrepareHead.reached ops AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install std B) D pub proof hash p input scratch source
#print axioms value
end AspisR1.FJt_PrepareHead
end
