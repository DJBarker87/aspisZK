import RPu_FJq_AlignedMessages
import RPu_FJq_SamplerErasure
import RPu_FJq_ChallengeLiteral
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_ArbitraryChallengeLiteral
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation SourceDigestAddresses SourceDigestLog SourceGlobalOracleInitial
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
/-- SAME source challenges in an arbitrary aligned literal proof, preserving
its full chronological sampler log via physical-message erasure. -/
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
    (rootBytes : bytes (decodeState root)=root0 p)
    (pf : RawCutProverCompiler.Proof)
    (aligned : Aligned p (LiteralTranscript.erasePrefix
      (eval H (F3J_SamplerRun.program pf 0 33 (FS.emptyPrefix pub))).2))
    (q : Fin 22 → Fin 262144) (v : LiteralOpeningView.View)
    (read : LiteralOpeningView.read (typedRows p q
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 0 33 (FS.emptyPrefix pub))).2))=some v) :
    v.semantic.map Prod.snd=FJq_ChallengeSlots.values c alpha := by
  let source:=F3J_InputRows.proof p (decodeState root) w bound
  have messages:=FJq_AlignedMessages.value H pf pub p (decodeState root) w bound rootBytes aligned
  have erased:=FJq_SamplerErasure.value H pf source 0 33 (FS.emptyPrefix pub) (FS.emptyPrefix pub) rfl
    (by intro k hk;simpa only [Nat.zero_add] using messages k hk)
  rw [erased.2] at read
  exact FJq_ChallengeLiteral.values trace count c alpha same init H backend p rows records w bound pub publicBytes q v read
#print axioms values
end AspisR1.FJq_ArbitraryChallengeLiteral
end
