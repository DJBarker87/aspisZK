import OraclePortFrozen2Roots

/-! Actual-run selected acceptance. All containing-log and frame identities
are derived. The result is on canonical restored rows carrying the compiler's
exact recorded-log words; it does not yet identify those rows with the legacy
arbitrary-constructor proof carrier in the global headline. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.OraclePortFrozen2ActualChecks
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortFrozen2Reached OraclePortFrozen2Roots
attribute [local irreducible] BinRawByteCutStability.recoverAt

theorem tail_root (frame : Bytes) (root : State)
    (read : BinRawByteCollisionTargets.pred 2 frame = some root) :
    RawCutWordsFromView.rootFrom 8 frame = root := by
  have same : RawByteCollisionTargets.trailing frame = some root := by
    simpa only [BinRawByteCollisionTargets.pred_tail,BinRawByteCollisionTargets.trailing,
      RawByteCollisionTargets.trailing] using read
  simp only [RawCutWordsFromView.rootFrom,RawByteCollisionTargets.pred_tail,same,Option.getD_some]

theorem middle_root (frame : Bytes) (root : State)
    (read : BinRawByteCollisionTargets.pred 3 frame = some root) :
    RawCutWordsFromView.rootFrom 9 frame = root := by
  have same : RawByteCollisionTargets.fixed 38 frame = some root := by
    simpa only [BinRawByteCollisionTargets.pred_middle,BinRawByteCollisionTargets.fixed,
      RawByteCollisionTargets.fixed] using read
  simp only [RawCutWordsFromView.rootFrom,RawByteCollisionTargets.pred_middle,same,Option.getD_some]

theorem maps_eq_builder (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (p : Parsed) (targets : ∀ k : Fin 3, BinRawByteCollisionTargets.pred (selectors k)
      (frames D P H k) = some (committedRoot p k.val)) :
    OraclePortFrozenOrderChecks.maps (run D P H).1 (frames D P H) p =
      BinCompiledRunWordStability.wordsFromRun D (view (run D P H)) := by
  have h0 := targets 0
  have h1 := targets 1
  have h2 := targets 2
  change BinRawByteCollisionTargets.pred 2
    (RawCutWordsFromView.frameFromView D (view (run D P H)) 0) = some (committedRoot p 0) at h0
  change BinRawByteCollisionTargets.pred 2
    (RawCutWordsFromView.frameFromView D (view (run D P H)) 2) = some (committedRoot p 1) at h1
  change BinRawByteCollisionTargets.pred 3
    (RawCutWordsFromView.frameFromView D (view (run D P H)) 30) = some (committedRoot p 2) at h2
  have r0 := tail_root _ _ h0
  have r1 := tail_root _ _ h1
  have r2 := middle_root _ _ h2
  unfold BinCompiledRunWordStability.wordsFromRun BinCanonicalCutWords.wordsFromRawCuts
  dsimp only
  rw [r0,r1,r2]
  rfl

/-- The parser, indexed recovery, scalar checks and semantic observations now
compose at the actual stored decision and original recorded log. No R13/R15/R3
or backend model premise is supplied by the caller. -/
theorem accepted_checks (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (Q : Nat) (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (accepted : (run D P H).2.2 = true)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred (Q+1161)) emptyTable (run D P H).1) :
    ∃ p q, OraclePortStoredParserC4.parseReached (input P H).stored (reached D P H) = some p ∧
      queries (reached D P H) = some q ∧
      Nonempty (LiteralAcceptanceTerminal.Checks (input P H).statement
        (OraclePortReaderPlumbingC6.reword
          (BinCompiledRunWordStability.wordsFromRun D (view (run D P H)))
          (OraclePortStoredDecisionDraftC4.typedRows p q (reached D P H)))) := by
  have decisionAccepted := OraclePortFrozen2Reached.accepted D P H accepted
  obtain ⟨_,p,q,_,parsed,query,_,_,_⟩ := OraclePortFrozen2.accepted_details _ _ _ H decisionAccepted
  have rootTargets := OraclePortFrozen2Roots.targets D P H accepted p q parsed query
  have checks := OraclePortFrozenOrderChecks.accepted_checks H (input P H).stored
    (reached D P H) (terminal P H) p q parsed query ((OraclePortFrozen2.acceptance_eq H _ _ _).symm.trans decisionAccepted) (run D P H).1 (Q+1161)
    (OraclePortFrozen2Reached.consistent D P H) (OraclePortFrozen2Reached.slots_read D P H accepted p q parsed query)
    (OraclePortFrozen2Reached.distinct_bound D P H Q hq) clean (frames D P H) selectors
    (fun k => OraclePortFrozen2Reached.frame_read D P H (frameRow k) (by
      fin_cases k <;> decide)) rootTargets
  rw [maps_eq_builder D P H p rootTargets] at checks
  exact ⟨p,q,parsed,query,checks⟩

#print axioms tail_root
#print axioms middle_root
#print axioms maps_eq_builder
#print axioms accepted_checks
end AspisR1.OraclePortFrozen2ActualChecks
end
