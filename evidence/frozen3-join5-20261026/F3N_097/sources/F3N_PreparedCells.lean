import F3N_Prepared
import F3N_SelectedDispatch
import F3N_PreparedClaim
import F3N_PreparedCoordinates
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_PreparedCells
open Aeneas Aeneas.Std Result
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge

theorem equality {H : Type} (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
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
    (meaning : OriginalPayloadClaimMeaning sem y1 inactive (toClaimE out.gamma)
      (toClaimE out.kappa) (toClaimE out.claim) g)
    (constant : i.data.c0=decode inactive)
    (claims : ∀ (point l : Usize) (hp : point.val<3) (hl : l.val<29) row scalar,
      Array.index_usize sem.claims point=ok row → Array.index_usize row l=ok scalar →
      LiteralOpeningView.eK (F3L_RhoMeaning.decode scalar)=i.data.Y ⟨point.val,by omega⟩ ⟨l.val,hl⟩)
    (extra : ∀ (l : Usize) (hl : l.val<29) scalar,
      Array.index_usize sem.extra l=ok scalar →
      LiteralOpeningView.eK (F3L_RhoMeaning.decode scalar)=i.data.Y 3 ⟨l.val,hl⟩)
    (before : ∀ (l : Usize) (hl : l.val<29) scalar,
      Array.index_usize sem.before_z1 l=ok scalar →
      LiteralOpeningView.eK (F3L_RhoMeaning.decode scalar)=i.data.Y 4 ⟨l.val,hl⟩)
    (final : ∀ (l : Usize) (hl : l.val<29) parsed,
      AspisR1CurrentPreparedClaim.ClaimParser.field y1 l=ok parsed → AspisR1CurrentPreparedClaim.Concrete.Canonical parsed →
      LiteralOpeningView.eK (F3L_RhoMeaning.decode (fromClaimQ parsed.c0))=i.data.Y 5 ⟨l.val,hl⟩) :
    F3L_SourcePrepared.numeric out=
      OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p i v)
        i.data (SelectedChallengeMap.rhoOf i.rho) q := by
  apply F3N_Prepared.equality sem y1 inactive out g p i v q six roots alpha
    point0 point1 block0 block1 points circle0 circle1 rs read challenge0 challenge1 meaning constant
  exact F3N_SelectedDispatch.selected sem y1 i.data.Y claims extra before final

#print axioms equality
end AspisR1.F3N_PreparedCells
end
