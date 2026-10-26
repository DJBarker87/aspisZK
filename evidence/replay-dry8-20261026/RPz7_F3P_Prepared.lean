import RPz7_F3P_SemanticClaimsY
import RPz7_F3P_SemanticY
import RPz7_F3P_GammaFrame
import RPz7_F3N_PreparedCells
import RPz7_F3N_SelectedDispatch
import RPz7_F3N_PreparedClaim
import RPz7_F3N_PreparedCoordinates
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_Prepared
open Aeneas Aeneas.Std Result
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge

theorem equality {H : Type} (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
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
      (OraclePortCompactDraft.slice p.wire 7031 464)) :
    F3L_SourcePrepared.numeric out=
      OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p i v)
        i.data (SelectedChallengeMap.rhoOf i.rho) q := by
  have claims := F3P_SemanticClaimsY.claims B std D pub semanticBytes hash sem pre parsed semantic p records q tr aligned i found
  have other := F3P_SemanticY.extra_before (ClaimsUnrolledFinish.install std B) D pub semanticBytes hash sem pre parsed semantic p records q tr aligned i found
  have final := F3P_GammaY.cells p q tr aligned i found y1 (F3P_GammaFrame.frame p y1 physical)
  exact F3N_PreparedCells.equality (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem)
    y1 inactive out g p i v q six roots alpha point0 point1 block0 block1 points circle0 circle1 rs read
    challenge0 challenge1 meaning constant claims other.1 other.2 final

#print axioms equality
end AspisR1.F3P_Prepared
end
