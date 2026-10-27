import RPz7_AuS1_Recovery
import RPz8_GExp_LowerTrace
import RPz7_GExq_FirstErasure
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_PrepareFrame
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open FS2.Duplex

theorem frame {Hash : Type} (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash) (source : ∀ h parts, D.digest h parts = hashv parts)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (proof : Slice U8) (hash : Hash)
    (p : verifier.Prepared) (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
      D pub proof hash none input = ok (.Ok p,scratch))
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire = MultiproofConeCanonical.bytesOf proof.val) :
    ∃ frame, Read (SdkC_Source.readLog (SdkC_Source.run hashv (SdkD_PrepareLower.lower
      (SdkD_PrepareSource.code ops B std D pub proof hash input)) []).2) frame ∧
      BinRawByteCollisionTargets.pred 3 frame = some (OraclePortBatchDraft.committedRoot parsed 2) := by
  have association : SdkD_PrepareLower.Associated hashv
      (SdkD_PrepareSource.code ops B std D pub proof hash input) :=
    GExp_PrepareAssociation.prepare ops AspisS1ExtractedRoundChildren.children
      (ClaimsUnrolledFinish.install std B) D pub proof hash input hashv source
  have logs := GExp_LowerTrace.log hashv (SdkD_PrepareSource.code ops B std D pub proof hash input) association
  rw [logs]
  exact AuS1_PrepareRead.frame ops B std D pub proof hash p input scratch success parsed wire

#print axioms frame
end AspisR1.GExq_PrepareFrame
end
