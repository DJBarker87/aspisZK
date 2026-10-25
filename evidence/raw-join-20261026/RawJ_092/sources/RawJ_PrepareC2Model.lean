import RawJ_PrepareC2
import SdkD_PhysicalRoots
import AuS1_Recovery
import GExp_LowerTrace
import GExq_FirstErasure
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_PrepareC2Model
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
    (parsed : OraclePortCompactDraft.Parsed)
    (parser : OraclePortCompactDraft.parse (MultiproofConeCanonical.bytesOf proof.val) = some parsed) (wire : parsed.wire = MultiproofConeCanonical.bytesOf proof.val) :
    ∃ frame, Read (SdkC_Source.readLog (SdkC_Source.run hashv (SdkD_PrepareLower.lower
      (SdkD_PrepareSource.code ops B std D pub proof hash input)) []).2) frame ∧
      BinRawByteCollisionTargets.pred 2 frame = some (OraclePortBatchDraft.committedRoot parsed 1) := by
  have association : SdkD_PrepareLower.Associated hashv
      (SdkD_PrepareSource.code ops B std D pub proof hash input) :=
    GExp_PrepareAssociation.prepare ops AspisS1ExtractedRoundChildren.children
      (ClaimsUnrolledFinish.install std B) D pub proof hash input hashv source
  have logs := GExp_LowerTrace.log hashv (SdkD_PrepareSource.code ops B std D pub proof hash input) association
  rw [logs]
  have erased := (SdkD_PrepareSource.source ops B std D pub proof hash input).trans success
  obtain ⟨frame,read,target⟩ := RawJ_PrepareC2.frame ops AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install std B) D pub proof hash p input scratch erased
  obtain ⟨root0,root1,roots,physical0,physical1⟩ := SdkD_PhysicalRoots.prepared ops B std D pub proof hash p input scratch success
  have first : Port3_BatchStage.root1 (Tx1Q_Carriers.prepared p) = root1 := by
    simp only [Port3_BatchStage.root1,Tx1Q_Carriers.prepared,roots,Array.make]
    rfl
  have physical : MultiproofConeCanonical.bytesOf root1.val = OraclePortCompactDraft.slice parsed.wire 63 32 := by
    rw [physical1,SdkD_ModelRoots.rawSlice,wire]
  have matched := SdkD_RootBinding.root1 (MultiproofConeCanonical.bytesOf proof.val) parsed parser root1 physical
  refine ⟨frame,read,?_⟩
  rw [first,matched] at target
  simpa only [AspisV8R19.SqueezeOracleBridge.state_roundtrip] using target

#print axioms frame
end AspisR1.RawJ_PrepareC2Model
end
