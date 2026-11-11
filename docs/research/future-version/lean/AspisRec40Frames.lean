import BinCompiledRunWordStability
import OracleProgramRecording
import AspisRec40HitMass

/-! Aspis 40-row recorded experiment: replay, frame and word lemmas for the
40-row verifier with a terminal decision (`AspisRec40.Decision.verifier`).

Copies, 33 → 40, of `OracleDecisionFeasibilityCore.{lift_from, lift_verifier}`,
`OraclePortReplay.{sampler_reads, frameFromView_eq}`,
`OracleProgramReplay.transcript_eq_of_agrees` (specialised),
`RawCutWordsFromView.{verifier_reads_in_experiment, recorded_transcript_eq,
frameFromView_eq, frame_read}`, `OracleDecisionFeasibilityCompiler.commitment_cut_eq`,
`OraclePortWords.wordsFromRun_compiled_eq_original`,
`OraclePortSamplerPrefixDraft.{output_pair, words_prefix}` and
`Frozen2StartChargePrefix.{same_transcript, transcript_start_read}`.
R1's `frame`, `frameFromView`, `wordsFromRun` are reused unchanged: they read
`LiteralByteProtocol.protocol D`'s chains, which are the 40-row protocol's
(`Protocol.chain_eq`). -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.Frames
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open AspisR1 RawCutTranscriptRun
open RawCutProverCompiler (Public Proof Prover RunView experiment experiment_eval)
open OracleDecisionFeasibilityCore (Decision onBytes lift)
open RawCutWordsFromView (frame frameFromView)

abbrev pr (D : LiteralByteProtocol.Decoder) := AspisRows40.Protocol.protocol D
abbrev V (D : LiteralByteProtocol.Decoder) (d : Decision) := AspisRec40.Decision.verifier D d

/-- Copy of `OracleDecisionFeasibilityCore.lift_from`, 33 → 40. -/
theorem lift_from (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (pf : Proof)
    (n : Nat) (p : LiteralTranscript.Prefix) :
    AspisRec40.Decision.verifierFrom D (lift d) pf n p =
      FS2.verifierFrom (pr D) (decisionOnBytes d) pf n p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    change bind _ (fun c => AspisRec40.Decision.verifierFrom D (lift d) pf n _) = bind _ (fun c => _)
    congr 1
    funext c
    exact ih _

theorem lift_verifier (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (pub : Public) (pf : Proof) :
    V D (lift d) pub pf = AspisRows40.Starts.verifier D d pub pf :=
  lift_from D d pf 40 (emptyPrefix pub)

theorem lift_verifier_fun (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) :
    V D (lift d) = AspisRows40.Starts.verifier D d := by
  funext pub pf
  exact lift_verifier D d pub pf

/-- Copy of `OraclePortReplay.sampler_reads`, 33 → 40. -/
theorem sampler_reads (D : LiteralByteProtocol.Decoder) (d : Decision) (H : Bytes → State)
    (pub : Public) (pf : Proof) (i : Nat) (hi : i < 40) (a : Bytes)
    (ha : a ∈ (eval H ((pr D).chain H pub pf i).toProgram).1.map Prod.fst) :
    a ∈ (eval H (V D d pub pf)).1.map Prod.fst := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
  apply List.mem_map.mpr
  refine ⟨q, ?_, rfl⟩
  rw [AspisRec40.Decision.verifier_eval]
  apply List.mem_append_left
  exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, hq⟩

/-- Copy of `OracleProgramReplay.transcript_eq_of_agrees` for the decision verifier. -/
theorem transcript_eq_of_agrees (D : LiteralByteProtocol.Decoder) (d : Decision)
    (H H' : Bytes → State) (pub : Public) (pf : Proof)
    (h : ∀ a ∈ (eval H (V D d pub pf)).1.map Prod.fst, H' a = H a)
    (n : Nat) (hn : n ≤ 40) : (pr D).transcript H' pub pf n = (pr D).transcript H pub pf n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hp := ih (by omega)
      have he : eval H' ((pr D).chain H pub pf n).toProgram =
          eval H ((pr D).chain H pub pf n).toProgram := by
        apply OracleProgramReplay.eval_eq_of_agrees
        intro a ha
        exact h a (sampler_reads D d H pub pf n (by omega) a ha)
      change ((pr D).transcript H' pub pf n).ext ((pr D).msg pf n)
        (eval H' ((pr D).samp n ((pr D).transcript H' pub pf n) ((pr D).msg pf n)).toProgram).2 = _
      rw [hp]
      change ((pr D).transcript H pub pf n).ext ((pr D).msg pf n)
        (eval H' ((pr D).chain H pub pf n).toProgram).2 = _
      rw [he]
      rfl

theorem verifier_reads_in_experiment (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) (a : Bytes)
    (ha : a ∈ (eval H (V D d
      (eval H (experiment P (V D d))).2.1.1 (eval H (experiment P (V D d))).2.1.2)).1.map Prod.fst) :
    a ∈ (eval H (experiment P (V D d))).1.map Prod.fst := by
  rw [RawCutProverCompiler.experiment_eval] at ha ⊢
  simp only [List.map_append]
  exact List.mem_append.mpr (Or.inr ha)

/-- Copy of `RawCutWordsFromView.recorded_transcript_eq`, 33 → 40. -/
theorem recorded_transcript_eq (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) (i : Nat) (hi : i ≤ 40) :
    let v := eval H (experiment P (V D d))
    (pr D).transcript (OracleProgramReplay.oracleOf v.1) v.2.1.1 v.2.1.2 i =
      (pr D).transcript H v.2.1.1 v.2.1.2 i := by
  dsimp only
  apply transcript_eq_of_agrees D d H
  · intro a ha
    exact OracleProgramReplay.oracleOf_eq H _ (FS.eval_consistent H _) a
      (verifier_reads_in_experiment D d P H a ha)
  · exact hi

/-- R1's `frame` is the first cell of the 40-row protocol's chain. -/
theorem frame_eq (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : Public) (pf : Proof) (i : Nat) :
    frame D H pub pf i = (firstCell ((pr D).chain H pub pf i)).getD [] := by
  unfold frame
  rw [AspisRows40.Protocol.chain_eq]

/-- Copy of `RawCutWordsFromView.frameFromView_eq`, 33 → 40. -/
theorem frameFromView_eq (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) (i : Nat) (hi : i ≤ 40) :
    let v := eval H (experiment P (V D d))
    frameFromView D v i = frame D H v.2.1.1 v.2.1.2 i := by
  dsimp only
  unfold frameFromView
  rw [frame_eq, frame_eq]
  unfold FS2.Protocol.chain
  rw [recorded_transcript_eq D d P H i hi]

private theorem firstCell_mem (H : Bytes → State)
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

/-- The first cell of every 40-row chain exists. -/
theorem chain_firstCell (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : Public) (pf : Proof) (i : Nat) :
    firstCell ((pr D).chain H pub pf i) ≠ none := by
  have hmap {I J A C : Type} [DecidableEq I] [Inhabited A]
      (label : I → J) (s : Sampler I A C) :
      firstCell (ProgramSamplerMap.map label s) = (firstCell s).map label := by
    cases s <;> rfl
  change firstCell (ProgramSamplerMap.map Addr.toBytes _) ≠ none
  rw [hmap]
  have hb : firstCell (LiteralTranscript.samp i ((pr D).transcript H pub pf i) ((pr D).msg pf i)) ≠ none :=
    UnifiedSampler.firstCell_some _ _ _ _ _
  simpa using hb

theorem frame_firstCell (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : Public) (pf : Proof) (i : Nat) :
    firstCell ((pr D).chain H pub pf i) = some (frame D H pub pf i) := by
  rw [frame_eq]
  cases h : firstCell ((pr D).chain H pub pf i) with
  | none => exact False.elim (chain_firstCell D H pub pf i h)
  | some a => rfl

/-- Copy of `RawCutWordsFromView.frame_read`, 33 → 40. -/
theorem frame_read (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) (i : Nat) (hi : i < 40) :
    let v := eval H (experiment P (V D d))
    Read v.1 (frame D H v.2.1.1 v.2.1.2 i) := by
  dsimp only
  apply verifier_reads_in_experiment D d P H
  apply sampler_reads D d H _ _ i hi
  exact firstCell_mem H _ _ (frame_firstCell D H _ _ i)

/-- Copy of `OracleDecisionFeasibilityCompiler.commitment_cut_eq`. -/
theorem commitment_cut_eq (D : LiteralByteProtocol.Decoder) (d : Decision)
    (buildWords : RunView → CanonicalCutEnrichedTranscript.Words) (P : Prover)
    (H : Bytes → State) (f : Bytes)
    (hf : Read (eval H (experiment P (V D d))).1 f) :
    BinRawByteCutRecovery.cut
        (eval H (experiment (AspisRec40.Decision.compiled D d buildWords P) (V D d))).1 f =
      BinRawByteCutRecovery.cut (eval H (experiment P (V D d))).1 f := by
  rw [AspisRec40.Decision.compiled_experiment_eval]
  exact OracleProgramRecording.cut_append_of_read f _ _ hf

/-- Copy of `OraclePortWords.wordsFromRun_compiled_eq_original`. -/
theorem wordsFromRun_compiled_eq_original (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) :
    BinCompiledRunWordStability.wordsFromRun D (eval H (experiment
      (AspisRec40.Decision.compiled D d (BinCompiledRunWordStability.wordsFromRun D) P) (V D d))) =
    BinCompiledRunWordStability.wordsFromRun D (eval H (experiment P (V D d))) := by
  let original := eval H (experiment P (V D d))
  let annotated := eval H (experiment
    (AspisRec40.Decision.compiled D d (BinCompiledRunWordStability.wordsFromRun D) P) (V D d))
  have hpub : annotated.2.1.1 = original.2.1.1 := by
    dsimp only [annotated, original]
    rw [AspisRec40.Decision.compiled_experiment_eval]
  have hproof : annotated.2.1.2 =
      RawCutTranscriptRun.proof (BinCompiledRunWordStability.wordsFromRun D original) original.2.1.2 := by
    dsimp only [annotated, original]
    rw [AspisRec40.Decision.compiled_experiment_eval]
  have frames (row : Nat) (hrow : row < 33) :
      frameFromView D annotated row = frameFromView D original row := by
    rw [frameFromView_eq D d
      (AspisRec40.Decision.compiled D d (BinCompiledRunWordStability.wordsFromRun D) P) H row (by omega),
      frameFromView_eq D d P H row (by omega)]
    change frame D H annotated.2.1.1 annotated.2.1.2 row =
      frame D H original.2.1.1 original.2.1.2 row
    rw [hpub, hproof]
    exact congrArg (fun s => (firstCell s).getD [])
      (RawCutTranscriptRun.chain_eq D (BinCompiledRunWordStability.wordsFromRun D original)
        H original.2.1.1 original.2.1.2 row)
  have cuts (row : Nat) (hrow : row < 33) :
      BinRawByteCutRecovery.cut annotated.1 (frameFromView D original row) =
      BinRawByteCutRecovery.cut original.1 (frameFromView D original row) := by
    have hf : Read original.1 (frameFromView D original row) := by
      rw [frameFromView_eq D d P H row (by omega)]
      exact frame_read D d P H row (by omega)
    exact commitment_cut_eq D d (BinCompiledRunWordStability.wordsFromRun D) P H _ hf
  change BinCompiledRunWordStability.wordsFromRun D annotated =
    BinCompiledRunWordStability.wordsFromRun D original
  unfold BinCompiledRunWordStability.wordsFromRun
  rw [frames 0 (by decide), frames 2 (by decide), frames 30 (by decide)]
  unfold BinCanonicalCutWords.wordsFromRawCuts
    BinCanonicalCutWords.rawC1Map BinCanonicalCutWords.rawC2Map
    BinCanonicalCutWords.rawFoldedMap
  dsimp only
  rw [cuts 0 (by decide), cuts 2 (by decide), cuts 30 (by decide)]

/-- Copy of `OraclePortSamplerPrefixDraft.output_pair`. -/
theorem output_pair (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) :
    (eval H (AspisRec40.Decision.original D d P)).2.1 = (AspisRec40.Decision.base D P H).2.1 := by
  rw [AspisRec40.Decision.original, RawCutProverCompiler.experiment_eval]
  unfold AspisRec40.Decision.base
  rw [RawCutProverCompiler.experiment_eval]

/-- The always-true base experiment is the decision experiment at `lift`. -/
theorem base_lift (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    AspisRec40.Decision.base D P H = eval H (experiment P (V D (lift (fun _ _ => true)))) := by
  unfold AspisRec40.Decision.base
  rw [lift_verifier_fun]

/-- Copy of `OraclePortSamplerPrefixDraft.words_prefix`. -/
theorem words_prefix (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) :
    BinCompiledRunWordStability.wordsFromRun D (eval H (AspisRec40.Decision.original D d P)) =
      BinCompiledRunWordStability.wordsFromRun D (AspisRec40.Decision.base D P H) := by
  have hf (n : Nat) (hn : n < 33) :
      frameFromView D (eval H (AspisRec40.Decision.original D d P)) n =
        frameFromView D (AspisRec40.Decision.base D P H) n := by
    have full : frameFromView D (eval H (AspisRec40.Decision.original D d P)) n =
        frame D H (eval H (AspisRec40.Decision.original D d P)).2.1.1
          (eval H (AspisRec40.Decision.original D d P)).2.1.2 n :=
      frameFromView_eq D d P H n (by omega)
    have prior : frameFromView D (AspisRec40.Decision.base D P H) n =
        frame D H (AspisRec40.Decision.base D P H).2.1.1 (AspisRec40.Decision.base D P H).2.1.2 n := by
      rw [base_lift]
      exact frameFromView_eq D _ P H n (by omega)
    rw [full, prior, output_pair]
  have hc (n : Nat) (hn : n < 33) :
      BinRawByteCutRecovery.cut (eval H (AspisRec40.Decision.original D d P)).1
          (frameFromView D (AspisRec40.Decision.base D P H) n) =
        BinRawByteCutRecovery.cut (AspisRec40.Decision.base D P H).1
          (frameFromView D (AspisRec40.Decision.base D P H) n) := by
    rw [AspisRec40.Decision.split_trace]
    apply OracleProgramRecording.cut_append_of_read
    rw [base_lift]
    rw [frameFromView_eq D _ P H n (by omega)]
    exact frame_read D _ P H n (by omega)
  unfold BinCompiledRunWordStability.wordsFromRun
  rw [hf 0 (by decide), hf 2 (by decide), hf 30 (by decide)]
  unfold BinCanonicalCutWords.wordsFromRawCuts BinCanonicalCutWords.rawC1Map
    BinCanonicalCutWords.rawC2Map BinCanonicalCutWords.rawFoldedMap
  dsimp only
  rw [hc 0 (by decide), hc 2 (by decide), hc 30 (by decide)]

#print axioms lift_verifier
#print axioms sampler_reads
#print axioms transcript_eq_of_agrees
#print axioms recorded_transcript_eq
#print axioms frameFromView_eq
#print axioms frame_read
#print axioms commitment_cut_eq
#print axioms wordsFromRun_compiled_eq_original
#print axioms output_pair
#print axioms base_lift
#print axioms words_prefix

end AspisRec40.Frames
end
