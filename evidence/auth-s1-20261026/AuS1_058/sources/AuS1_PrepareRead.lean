import AuS1_ClosedRead
import AuS1_RootSource
import AuS1_Observe
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_PrepareRead
open Aeneas Aeneas.Std Result
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation.PreparedHashCode
open AspisR1CurrentCaller InstalledPreparation
open MultiproofConeCanonical
attribute [local irreducible] SdkD_PrepareSource.code

 theorem frame (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
      D pub proof hash none input = ok (.Ok p,scratch))
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire = bytesOf proof.val) :
    ∃ frame, Read (observe (run (SdkD_PrepareSource.code ops B std D pub proof hash input)).1) frame ∧
      BinRawByteCollisionTargets.pred 3 frame = some (OraclePortBatchDraft.committedRoot parsed 2) := by
  have erased : erase (SdkD_PrepareSource.code ops B std D pub proof hash input) = ok (.Ok p,scratch) :=
    (SdkD_PrepareSource.source ops B std D pub proof hash input).trans success
  unfold SdkD_PrepareSource.code at erased ⊢
  obtain ⟨semantic,y1,view,sem,hview,original,contains⟩ :=
    AuS1_Enclosing.reached ops AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std B)
      D pub proof hash p input scratch erased
  obtain ⟨root,folded,model⟩ := AuS1_RootSource.model proof semantic y1 view hview parsed wire
  obtain ⟨frame,read,target⟩ := AuS1_ClosedRead.frame D sem view hash input scratch p root
    (sourceView_variant proof semantic y1 view hview) folded original
  exact ⟨frame,contains frame read,by rw [target,model]⟩

#print axioms frame
end AspisR1.AuS1_PrepareRead
end
