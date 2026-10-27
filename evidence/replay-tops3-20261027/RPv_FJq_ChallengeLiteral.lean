import RPv_FJq_SourceChallengeMap
import RPz7_F3M_OpeningChallenges
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_ChallengeLiteral
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation SourceDigestAddresses SourceDigestLog SourceGlobalOracleInitial
open OraclePortCompactDraft
/-- Exact SAME source trace and literal sampler operands, including public bytes.
The association of this source-built pf with the deployed proof is downstream. -/
theorem values {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (trace : SourceFull25.Trace D pre before after cs) (count : cs.length=25)
    (c : r1_wire.Challenges) (alpha : Array aspis_core.field.QM31 10#usize)
    (same : cs.map SourceFull25.Call.q=BeginCalls.challengeList c++alpha.val)
    {pubInput : pool_v1.pair_forest_semantic_terminal.r0.Public} {root : TranscriptStep.Bytes32}
    (init : PublicInitCall D pubInput root before)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic)
    (records : p.semantic=pre.records.val.map (fun s=>MultiproofConeCanonical.bytesOf s.val))
    (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (pub : LiteralTranscript.Public)
    (publicBytes : pub.pubBytes=rawBytes (alloc.vec.Vec.deref init.encoded))
    (q : Fin 22 → Fin 262144) (v : LiteralOpeningView.View)
    (read : LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program
        (F3J_InputRows.proof p (decodeState root) w bound) 0 33 (FS.emptyPrefix pub))).2))=some v) :
    v.semantic.map Prod.snd=FJq_ChallengeSlots.values c alpha := by
  have source:=F3M_First25Challenges.sampler trace count init H backend p rows records w bound
    (FS.emptyPrefix pub) publicBytes
  have literal:=F3M_OpeningChallenges.values H (F3J_InputRows.proof p (decodeState root) w bound)
    pub 8 p q v read
  rw [literal,source]
  exact FJq_SourceChallengeMap.values cs c alpha same
#print axioms values
end AspisR1.FJq_ChallengeLiteral
end
