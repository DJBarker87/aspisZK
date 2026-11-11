import AspisOneTxChecks
import AspisRows40Literal
import AspisRec40CallBudgetAspis
import OraclePortReachedRootsC6
import OraclePortActualAcceptanceC6

/-! The Aspis one-transaction verifier: item M7 of ONE-TRANSACTION-GAME.md, the
actual-run identification. "Accepted ⇒ AspisChecks" on the actual 40-row run of
the rows agent's experiment `AspisRec40.HitMass.original D dV_aspis P`.

Kind of result: MODEL THEOREMS in R1's stored-decision and binary commitment
model. Copies of R1's `OraclePortFrozen2Reached.{accepted, decision_read,
slots_read, consistent, distinct_bound, frame_read}`, `OraclePortFrozen2Roots.targets`
(via the draft-chain twin `OraclePortReachedRootsC6.targets`, whose body is
the same), `OraclePortFrozen2ActualChecks.{maps_eq_builder, accepted_checks}`
and `OraclePortStoredProjectionC4.frame_eq` / `OraclePortReplay.frameFromView_eq`,
for the 40-row run at `dV_aspis`. No two-transaction module is imported.

Differences: the run is the 40-row experiment; the decision is `dV_aspis`; the
first-read budget is `Q + 1111` (the rows agent's `verifier_issued`); the
reached prefix has 40 rounds and R1's 33-round reads apply to `take33`
(`reached_take33`: it IS R1's reached prefix on the same proof); the frame and
replay lemmas are re-proved for rows below 40 from the 40-row verifier's
evaluation (`AspisRec40.Decision.verifier_eval`) and `Protocol.chain_eq`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisOneTx.Run
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisR1 AspisR1.OraclePortStoredExperimentC4 AspisR1.OraclePortCompactDraft
open AspisR1.OraclePortSelectedDraft AspisR1.OraclePortBatchDraft
open AspisOneTx
open AspisAcceptance (AspisChecks)

abbrev input (P : Prover) (H : Bytes → State) := (eval H P).2
abbrev reached40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :=
  LiteralTranscript.erasePrefix
    ((AspisRows40.Protocol.protocol D).transcript H (input P H).statement (input P H).proof 40)
abbrev terminal40 (P : Prover) (H : Bytes → State) := LiteralTranscript.erase ((input P H).proof 40)
abbrev run40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :=
  eval H (AspisRec40.HitMass.original D dV_aspis P)

/-! ### R1's reads on the first 33 rounds -/

/-- The first 33 rounds of the 40-row reached prefix are R1's reached prefix. -/
theorem reached_take33 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    take33 (reached40 D P H) = OraclePortReachedRunC6.reached D P H := by
  obtain ⟨hs, hr⟩ := AspisRows40.Literal.transcript_take33 D _ H (input P H).statement
    (input P H).proof 40 (by omega)
  unfold take33 reached40 OraclePortReachedRunC6.reached OraclePortReachedRunC6.transcript
  unfold LiteralTranscript.erasePrefix
  rw [hs, ← List.map_take, hr]

/-! ### The run (copy of `OraclePortFrozen2Reached`) -/

theorem accepted40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (ha : (run40 D P H).2.2 = true) :
    (eval H (dV_aspis (input P H).stored (reached40 D P H) (terminal40 P H))).2 = true := by
  change (eval H (AspisRec40.HitMass.original D dV_aspis P)).2.2 = true at ha
  rw [AspisRec40.HitMass.original_eval] at ha
  change (eval H (AspisRec40.Decision.verifier D (dV_aspis (input P H).stored)
    (input P H).statement (input P H).proof)).2 = true at ha
  rw [AspisRec40.Decision.verifier_eval] at ha
  exact ha

theorem decision_read40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (a : Bytes) (read : Read (eval H (dV_aspis (input P H).stored
      (reached40 D P H) (terminal40 P H))).1 a) : Read (run40 D P H).1 a := by
  change Read (eval H (AspisRec40.HitMass.original D dV_aspis P)).1 a
  rw [AspisRec40.HitMass.original_eval]
  change Read ((eval H P).1 ++ (eval H (AspisRec40.Decision.verifier D
    (dV_aspis (input P H).stored) (input P H).statement (input P H).proof)).1) a
  rw [AspisRec40.Decision.verifier_eval]
  dsimp only
  simp only [Read,List.map_append,List.mem_append]
  exact Or.inr (Or.inr read)

theorem slots_read40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (ha : (run40 D P H).2.2 = true) (p : Parsed) (q : Fin 22 → Fin 262144)
    (parsed : parseReachedS (input P H).stored (reached40 D P H) = some p)
    (query : queries (take33 (reached40 D P H)) = some q) :
    ∀ a, Read (eval H (verifyMergedAll p q)).1 a → Read (run40 D P H).1 a := by
  obtain ⟨guard,len,p',q',i,hp,hq,_,_,_⟩ :=
    accepted_detailsS _ _ _ H (accepted40 D P H ha)
  have psame : p' = p := Option.some.inj (hp.symm.trans parsed)
  have qsame : q' = q := Option.some.inj (hq.symm.trans query)
  subst p'; subst q'
  intro a read
  apply decision_read40 D P H a
  simpa only [dV_aspis,if_pos (And.intro guard len),parsed,query,
    eval_bind,eval,List.append_nil] using read

theorem consistent40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    ∀ a ∈ (run40 D P H).1, a.2 = H a.1 := FS.eval_consistent H _

/-- The distinct first reads of the run: `Q + 1111` (136 transcript + 975 merged slots). -/
theorem distinct_bound40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (Q : Nat) (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    firstReads emptyTable (run40 D P H).1 ≤ Q+1111 := by
  have hv : (eval H (AspisRec40.HitMass.verifier D dV_aspis (eval H P).2)).1.length ≤ 1111 :=
    AspisRec40.CallBudgetAspis.verifier_issued D (input P H).stored H
      (input P H).statement (input P H).proof
  have hl := VerifierCallBudget.firstReads_le_length emptyTable
    (eval H (AspisRec40.HitMass.original D dV_aspis P)).1
  have hp := hq H
  change firstReads emptyTable (eval H (AspisRec40.HitMass.original D dV_aspis P)).1 ≤ _
  rw [AspisRec40.HitMass.original_eval] at hl ⊢
  dsimp only at hl ⊢
  rw [List.length_append] at hl
  omega

/-! ### Frames of the run (copy of `frame_eq` / `frameFromView_eq` / `frame_read`) -/

/-- Every read of a sampler row below 40 is in the run's log. -/
theorem chain_reads40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (j : Nat) (hj : j < 40) (a : Bytes)
    (ha : a ∈ (eval H ((LiteralByteProtocol.protocol D).chain H (input P H).statement
      (input P H).proof j).toProgram).1.map Prod.fst) :
    a ∈ (run40 D P H).1.map Prod.fst := by
  rw [← AspisRows40.Protocol.chain_eq] at ha
  change a ∈ (eval H (AspisRec40.HitMass.original D dV_aspis P)).1.map Prod.fst
  rw [AspisRec40.HitMass.original_eval]
  change a ∈ ((eval H P).1 ++ (eval H (AspisRec40.Decision.verifier D
    (dV_aspis (input P H).stored) (input P H).statement (input P H).proof)).1).map Prod.fst
  rw [AspisRec40.Decision.verifier_eval]
  dsimp only
  simp only [List.map_append,List.mem_append]
  refine Or.inr (Or.inl ?_)
  obtain ⟨x, hx, hxa⟩ := List.mem_map.mp ha
  exact List.mem_map.mpr ⟨x, List.mem_flatten.mpr ⟨_, List.mem_map.mpr
    ⟨j, List.mem_range.mpr hj, rfl⟩, hx⟩, hxa⟩

/-- `transcript_eq_of_agrees` with the agreement stated on the chains' reads. -/
theorem transcript_eq_of_chains (D : LiteralByteProtocol.Decoder) (H H' : Bytes → State)
    (x : LiteralTranscript.Public) (pf : LiteralByteProtocol.Proof) :
    ∀ n, (∀ j, j < n → ∀ a ∈ (eval H ((LiteralByteProtocol.protocol D).chain H x pf j).toProgram).1.map
      Prod.fst, H' a = H a) →
      (LiteralByteProtocol.protocol D).transcript H' x pf n =
        (LiteralByteProtocol.protocol D).transcript H x pf n
  | 0, _ => rfl
  | n + 1, h => by
      have hp := transcript_eq_of_chains D H H' x pf n (fun j hj => h j (by omega))
      have he : eval H' ((LiteralByteProtocol.protocol D).chain H x pf n).toProgram =
          eval H ((LiteralByteProtocol.protocol D).chain H x pf n).toProgram :=
        OracleProgramReplay.eval_eq_of_agrees H H' _ (h n (by omega))
      change ((LiteralByteProtocol.protocol D).transcript H' x pf n).ext
        ((LiteralByteProtocol.protocol D).msg pf n)
        (eval H' ((LiteralByteProtocol.protocol D).samp n
          ((LiteralByteProtocol.protocol D).transcript H' x pf n)
          ((LiteralByteProtocol.protocol D).msg pf n)).toProgram).2 = _
      rw [hp]
      change ((LiteralByteProtocol.protocol D).transcript H x pf n).ext
        ((LiteralByteProtocol.protocol D).msg pf n)
        (eval H' ((LiteralByteProtocol.protocol D).chain H x pf n).toProgram).2 = _
      rw [he]
      rfl

theorem view_run40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    view (run40 D P H) = ((run40 D P H).1,
      (((input P H).statement,(input P H).proof),(run40 D P H).2.2)) := by
  change view (eval H (AspisRec40.HitMass.original D dV_aspis P)) = _
  simp only [view, AspisRec40.HitMass.original_eval]

theorem frame_eq40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (n : Nat) (hn : n ≤ 40) :
    RawCutWordsFromView.frameFromView D (view (run40 D P H)) n =
      RawCutWordsFromView.frame D H (input P H).statement (input P H).proof n := by
  rw [view_run40]
  dsimp only [RawCutWordsFromView.frameFromView, RawCutWordsFromView.frame, Protocol.chain]
  rw [transcript_eq_of_chains D H _ _ _ n (fun j hj a ha =>
    OracleProgramReplay.oracleOf_eq H _ (consistent40 D P H) a
      (chain_reads40 D P H j (by omega) a ha))]

theorem firstCell_mem40 (H : Bytes → State)
    (s : Sampler Bytes State LiteralTranscript.Challenge) (a : Bytes)
    (ha : firstCell s = some a) : a ∈ (eval H s.toProgram).1.map Prod.fst := by
  cases s with
  | done c => cases ha
  | ask i k =>
      simp only [FS2.firstCell, Option.some.injEq] at ha
      subst i
      exact List.mem_cons_self ..
  | multi c cs nd k =>
      simp only [FS2.firstCell, Option.some.injEq] at ha
      subst c
      exact List.mem_cons_self ..

/-- Every sampler frame below 40 (in particular the three commitment frames)
was read in the run. -/
theorem frame_read40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (row : Nat) (bound : row < 40) :
    Read (run40 D P H).1 (RawCutWordsFromView.frameFromView D (view (run40 D P H)) row) := by
  rw [frame_eq40 D P H row (by omega)]
  have hbounded : firstCell (LiteralTranscript.samp row
      ((LiteralByteProtocol.protocol D).transcript H (input P H).statement (input P H).proof row)
      ((LiteralByteProtocol.protocol D).msg (input P H).proof row)) ≠ none :=
    UnifiedSampler.firstCell_some _ _ _ _ _
  have hmap {I J A C : Type} [DecidableEq I] [Inhabited A]
      (label : I → J) (s : Sampler I A C) :
      firstCell (ProgramSamplerMap.map label s) = (firstCell s).map label := by
    cases s <;> rfl
  have hn : firstCell ((LiteralByteProtocol.protocol D).chain H
      (input P H).statement (input P H).proof row) ≠ none := by
    change firstCell (ProgramSamplerMap.map Addr.toBytes _) ≠ none
    rw [hmap]
    simpa using hbounded
  unfold RawCutWordsFromView.frame
  cases h : firstCell ((LiteralByteProtocol.protocol D).chain H
      (input P H).statement (input P H).proof row) with
  | none => exact False.elim (hn h)
  | some a =>
    simp only [Option.getD_some]
    exact chain_reads40 D P H row bound a (firstCell_mem40 H _ a h)

/-! ### Roots (copy of `OraclePortFrozen2Roots.targets`) -/

section roots
attribute [local irreducible] LiteralByteProtocol.protocol LiteralByteSampler.samp

abbrev frames40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) (k : Fin 3) : Bytes :=
  RawCutWordsFromView.frameFromView D (view (run40 D P H)) (OraclePortReachedRootsC6.frameRow k)

theorem targets40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (ha : (run40 D P H).2.2 = true) (p : Parsed) (q : Fin 22 → Fin 262144)
    (parsed : parseReachedS (input P H).stored (reached40 D P H) = some p)
    (query : queries (take33 (reached40 D P H)) = some q) :
    ∀ k : Fin 3, BinRawByteCollisionTargets.pred (OraclePortReachedRootsC6.selectors k)
      (frames40 D P H k) = some (committedRoot p k.val) := by
  obtain ⟨_,_,p',q',i,hp,hq,_,input',checked⟩ := accepted_detailsS _ _ _ H (accepted40 D P H ha)
  have psame : p' = p := Option.some.inj (hp.symm.trans parsed)
  have qsame : q' = q := Option.some.inj (hq.symm.trans query)
  subst p'; subst q'
  have matching : LiteralMatchingData.read (OraclePortStoredDecisionDraftC4.typedRows p q
      (OraclePortReachedRunC6.reached D P H)) = some i.data := by
    rw [← reached_take33, ← typedRows_take]; exact (verifyS_accepted _ i checked).1
  have aligned := (parsedS _ _ p parsed).2.2.1
  rw [reached_take33] at aligned
  obtain ⟨_,_,_,⟨root0,c0,row0,bytes0⟩,rows⟩ := aligned
  obtain ⟨c0',at0⟩ := OraclePortReachedRootsC6.erased_index D P H 0 (by decide)
  have msg0 : LiteralTranscript.erase ((input P H).proof 0) = .initial root0 :=
    congrArg Prod.fst (Option.some.inj (at0.symm.trans row0))
  have root0same := OraclePortRootBytesC6.initial p root0 bytes0.symm
  have h0 : BinRawByteCollisionTargets.pred 2 (frames40 D P H 0) = some (committedRoot p 0) := by
    change BinRawByteCollisionTargets.pred 2 (RawCutWordsFromView.frameFromView D (view (run40 D P H)) 0) = _
    rw [frame_eq40 D P H 0 (by decide),root0same]
    exact OraclePortFrameShapesC6.initial_target D H _ _ root0 msg0
  obtain ⟨b2,c2,row2,bytes2⟩ := rows 2 (by decide) (by decide)
  obtain ⟨c2',at2⟩ := OraclePortReachedRootsC6.erased_index D P H 2 (by decide)
  have msg2 : LiteralTranscript.erase ((input P H).proof 2) = .payload b2 :=
    congrArg Prod.fst (Option.some.inj (at2.symm.trans row2))
  obtain ⟨root1,encoded2⟩ := OraclePortParsedRootsC6.c2_record p q
    (OraclePortReachedRunC6.reached D P H) i.data matching b2 c2 row2
  have record2 : p.semantic[2]?.getD [] = b2.val := by
    simpa only [rowBytes,show (2:Nat) < 27 by decide,ite_true] using bytes2.symm
  have root1same := OraclePortRootBytesC6.second p root1 (record2.trans encoded2)
  have h1 : BinRawByteCollisionTargets.pred 2 (frames40 D P H 1) = some (committedRoot p 1) := by
    change BinRawByteCollisionTargets.pred 2 (RawCutWordsFromView.frameFromView D (view (run40 D P H)) 2) = _
    rw [frame_eq40 D P H 2 (by decide),root1same]
    rw [OraclePortFrameShapesC6.ordinary D H _ _ 2 (by decide) (by decide) (by decide) b2 msg2,
      OraclePortFrameShapesC6.absorb_bytes,encoded2,BinRawByteCollisionTargets.pred_tail]
    change BinRawByteCollisionTargets.trailing
      (_ ++ [0,SelectedTranscriptParams.label 2] ++ RecordFrameCodec.frame 1 (bytes root1)) = some root1
    simpa only [RecordFrameCodec.frame,List.append_assoc] using
      BinRawByteCollisionTargets.trailing_frame
        (bytes (UnifiedSampler.stateOf SelectedTranscriptParams.params
          (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
            (input P H).statement (input P H).proof 2))) ++ [0,SelectedTranscriptParams.label 2] ++
          RecordFrameCodec.header 1 (bytes root1).length) root1
  obtain ⟨b30,c30,row30,bytes30⟩ := rows 30 (by decide) (by decide)
  obtain ⟨c30',at30⟩ := OraclePortReachedRootsC6.erased_index D P H 30 (by decide)
  have msg30 : LiteralTranscript.erase ((input P H).proof 30) = .payload b30 :=
    congrArg Prod.fst (Option.some.inj (at30.symm.trans row30))
  obtain ⟨payload,encoded30⟩ := OraclePortParsedRootsC6.folded_record p q
    (OraclePortReachedRunC6.reached D P H) i.data matching b30 c30 row30
  have root2same := OraclePortRootBytesC6.folded p payload (bytes30.symm.trans encoded30)
  have h2 : BinRawByteCollisionTargets.pred 3 (frames40 D P H 2) = some (committedRoot p 2) := by
    change BinRawByteCollisionTargets.pred 3 (RawCutWordsFromView.frameFromView D (view (run40 D P H)) 30) = _
    rw [frame_eq40 D P H 30 (by decide),root2same]
    rw [OraclePortFrameShapesC6.ordinary D H _ _ 30 (by decide) (by decide) (by decide) b30 msg30,
      OraclePortFrameShapesC6.absorb_bytes,encoded30,BinRawByteCollisionTargets.pred_middle]
    let state := UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
        (input P H).statement (input P H).proof 30))
    let tail := SelectedFieldSequenceCodec.encodeWide payload.2
    let pre := bytes state ++ [0,SelectedTranscriptParams.label 30] ++
      PublicInitFrame.lengthBytes (bytes payload.1 ++ tail).length
    have prelen : pre.length = 38 := by
      simp only [pre,List.length_append,bytes_length,List.length_cons,List.length_nil,PublicInitFrame.lengthBytes_length]
    have encode : OpeningRecordCodec.encode payload =
        LengthFrameCodec.frame (bytes payload.1 ++ SelectedFieldSequenceCodec.encodeWide payload.2) := by
      cases payload
      rfl
    simpa only [encode,LengthFrameCodec.frame,pre,tail,state,input,List.append_assoc] using
      BinRawByteCollisionTargets.fixed_frame 38 pre payload.1 tail prelen
  intro k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
end roots

/-! ### Accepted ⇒ AspisChecks on the actual run (copy of `OraclePortFrozen2ActualChecks`) -/

theorem maps_eq_builder40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (p : Parsed) (targets : ∀ k : Fin 3, BinRawByteCollisionTargets.pred
      (OraclePortReachedRootsC6.selectors k) (frames40 D P H k) = some (committedRoot p k.val)) :
    OraclePortFrozenOrderChecks.maps (run40 D P H).1 (frames40 D P H) p =
      BinCompiledRunWordStability.wordsFromRun D (view (run40 D P H)) := by
  have h0 := targets 0
  have h1 := targets 1
  have h2 := targets 2
  change BinRawByteCollisionTargets.pred 2
    (RawCutWordsFromView.frameFromView D (view (run40 D P H)) 0) = some (committedRoot p 0) at h0
  change BinRawByteCollisionTargets.pred 2
    (RawCutWordsFromView.frameFromView D (view (run40 D P H)) 2) = some (committedRoot p 1) at h1
  change BinRawByteCollisionTargets.pred 3
    (RawCutWordsFromView.frameFromView D (view (run40 D P H)) 30) = some (committedRoot p 2) at h2
  have r0 := OraclePortActualAcceptanceC6.tail_root _ _ h0
  have r1 := OraclePortActualAcceptanceC6.tail_root _ _ h1
  have r2 := OraclePortActualAcceptanceC6.middle_root _ _ h2
  unfold BinCompiledRunWordStability.wordsFromRun BinCanonicalCutWords.wordsFromRawCuts
  dsimp only
  rw [r0,r1,r2]
  rfl

/-- M7: on the actual 40-row run at `dV_aspis`, acceptance and R1's single
collision event at `Q + 1111` give `AspisChecks` on the recorded words. -/
theorem accepted_checks40 (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (Q : Nat) (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (accepted : (run40 D P H).2.2 = true)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred (Q+1111)) emptyTable (run40 D P H).1) :
    ∃ p q, parseReachedS (input P H).stored (reached40 D P H) = some p ∧
      queries (take33 (reached40 D P H)) = some q ∧
      Nonempty (AspisChecks decodePairS (reached40 D P H).statement
        (OraclePortReaderPlumbingC6.reword
          (BinCompiledRunWordStability.wordsFromRun D (view (run40 D P H)))
          (OraclePortStoredDecisionDraftC4.typedRows p q (reached40 D P H)))) := by
  have decisionAccepted := accepted40 D P H accepted
  obtain ⟨_,_,p,q,_,parsed,query,_,_,_⟩ := accepted_detailsS _ _ _ H decisionAccepted
  have rootTargets := targets40 D P H accepted p q parsed query
  have checks := accepted_checks_aspis H (input P H).stored (reached40 D P H) (terminal40 P H)
    p q parsed query decisionAccepted (run40 D P H).1 (Q+1111) (consistent40 D P H)
    (slots_read40 D P H accepted p q parsed query) (distinct_bound40 D P H Q hq) clean
    (frames40 D P H) OraclePortReachedRootsC6.selectors
    (fun k => frame_read40 D P H (OraclePortReachedRootsC6.frameRow k) (by
      fin_cases k <;> decide)) rootTargets
  rw [maps_eq_builder40 D P H p rootTargets] at checks
  exact ⟨p,q,parsed,query,checks⟩

#print axioms reached_take33
#print axioms accepted40
#print axioms decision_read40
#print axioms slots_read40
#print axioms distinct_bound40
#print axioms chain_reads40
#print axioms transcript_eq_of_chains
#print axioms frame_eq40
#print axioms frame_read40
#print axioms targets40
#print axioms maps_eq_builder40
#print axioms accepted_checks40
end AspisOneTx.Run
end
