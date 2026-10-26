import F3N_ModelBody
import F3P_CheckpointSaved
import F3P_Prepared
import F3P_SemanticClaimsY
import F3P_SemanticY
import F3P_GammaFrame
import F3N_PreparedCells
import F3N_SelectedDispatch
import F3N_PreparedClaim
import F3N_PreparedCoordinates
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_CheckpointBody
open Aeneas Aeneas.Std Result
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge

theorem body {H : Type} (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (y1 : Slice U8) (inactive : E) (out : AspisR1PublicPreparation.verifier.Prepared)
    (g : Array E 29#usize) (p : OraclePortCompactDraft.Parsed)
    (i : RecordedBinaryExperimentBin.SourceInputs) (v : LiteralOpeningView.View)
    (q : Fin 22 → Fin 262144)
    (six : F3L_PreparedModelSix.Fields out i q)
    (roots : (F3L_SourcePrepared.numeric out).roots=(fun j=>OraclePortBatchDraft.committedRoot p j.val))
    (alpha : (F3L_SourcePrepared.numeric out).semanticAlpha=(OraclePortAcceptedContextC6.context p i v).semanticAlpha)
    (point0 point1 : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint)
    (block0 block1 : Array U8 32#usize)
    (points : out.z=Array.make 2#usize [point0,point1])
    (circle0 : F3M_CircleSource.source block0 .First=ok point0)
    (circle1 : F3M_CircleSource.source block1 .Second=ok point1)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (read : LiteralOpeningView.read rs=some v)
    (challenge0 : v.challenge25=SelectedTranscriptParams.params.σ 25 (AspisV8R19.SqueezeOracleBridge.decodeState block0))
    (challenge1 : v.challenge26=SelectedTranscriptParams.params.σ 26 (AspisV8R19.SqueezeOracleBridge.decodeState block1))
    (meaning : OriginalPayloadClaimMeaning (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem) y1 inactive (toClaimE out.gamma)
      (toClaimE out.kappa) (toClaimE out.claim) g)
    (constant : i.data.c0=decode inactive)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (semanticBytes : Slice U8) (hash : H) (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (parsed : AspisR1PublicPreparation.PrefixAdapter.parseAccepted semanticBytes=ok (.Ok pre))
    (semantic : AspisR1CurrentCaller.S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
      (ClaimsUnrolledFinish.install std B) D pub semanticBytes hash=ok (.Ok sem))
    (records : p.semantic=pre.records.val.map (fun s=>MultiproofConeCanonical.bytesOf s.val))
    (tr : RawCutTranscriptRun.ErasedPrefix) (aligned : OraclePortCompactDraft.Aligned p tr)
    (found : OraclePortStoredDecisionDraftC4.input p q tr=some i)
    (physical : MultiproofConeCanonical.bytesOf y1.val=OraclePortCompactDraft.expand 29
      (OraclePortCompactDraft.slice p.wire 7031 464))
    (V : VTop_Stages.aspis_core.digest.Digest32 H)
    (oracleH : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
    (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest V) hash oracleH)
    (acc : AspisR1Stage2.verifier.Accumulator) (proof publicBytes : Slice U8) (saved : alloc.vec.Vec U8)
    (size : acc.weights.val.length=64)
    (qb : ∀ j : Fin 22,((F3K_CheckpointPreparedFields.writerPrepared out).queries.val[j.val]'(by
      have h : (F3K_CheckpointPreparedFields.writerPrepared out).queries.val.length=22 :=
        (F3K_CheckpointPreparedFields.writerPrepared out).queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields
      (F3K_CheckpointPreparedFields.writerPrepared out) (CheckpointBytes3Namespaces.toAccumulator acc)
      (by simpa only [CheckpointBytes3Namespaces.toAccumulator,CheckpointBytes3Namespaces.mapVec,List.length_map] using size) qb))
    (next : acc.next.val=10)
    (writer : Port3_CheckpointInstall.writer V
      (Tx1Q_Carriers.prepared (AspisR1CurrentCaller.InstalledPreparation.currentPrepared out))
      acc proof publicBytes hash=ok saved)
    (ten : CheckpointBytes5Output.accumulator acc=
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q)).accumulator)
    (hp hu : Array U8 32#usize) :
    CheckpointBytesDecodeC5.sourceBody (F3K_CheckpointPreparedFields.writerPrepared out)
      (CheckpointBytes3Namespaces.toAccumulator acc) hp hu=
      OraclePortCheckpointAbiC5.body
        (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p i v)
          i.data (SelectedChallengeMap.rhoOf i.rho) q)
        (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
          (SelectedChallengeMap.rhoOf i.rho) q)).accumulator
        (CheckpointBytesDigest.stateOf hp) (CheckpointBytesDigest.stateOf hu) := by
  have prepared := F3P_Prepared.equality sem y1 inactive out g p i v q six roots alpha
    point0 point1 block0 block1 points circle0 circle1 rs read challenge0 challenge1 meaning constant
    B std D pub semanticBytes hash pre parsed semantic records tr aligned found physical
  exact F3N_ModelBody.body out acc hp hu size qb canonical next p i v q prepared ten

#print axioms body
end AspisR1.F3P_CheckpointBody
end
