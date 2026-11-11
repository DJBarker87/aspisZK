import RWireLiteralTableChoiceWords
import RWireRawCutLiteralAllFrames
import RWireRawCutLaterTableLiteralWords
import TraceAppend
import AspisRec40Frames
import AspisRec40CleanRun
import AspisRec40FinalShape

/-! Word choice for rows 33 to 39 (work order W3): the words the decoder
reads back from the table before row n's frame (33 ≤ n < 40) are the words of
the run (`wordsFromRun`). Copy of `RWireLiteralTableChoiceWords.constructed_components`
(which carries `n < 33`) on the 40-row run, with R1's premises and one more,
`AspisRec40.FinalShape.LatePayload` (rows 33 to 39 erase to payload messages).
Without it the statement is false: a `.initial` message at row n makes row n's
frame the squeeze frame of the initial vector, which a prover can read first.

Route:
- `split`: the 40-row run is R1's run (same prover, same decision) followed by
  the chains of rows 33 to 39, with the same output (as `CleanRun.base_split`).
- `adjacent40`: frames of rows i and i+1 (32 ≤ i < 39) are read in order, from
  R1's `BinRawByteCollisionTargets.duplex_state_before_frame` (the frame is read
  before its advance, the advance before the next frame); copies of R1's
  `RWireRawCutLiteralNextFrame.{next_frame_prefix, ordinary_next_prefix_state,
  ordinary_advance_read}` with the payload form of the row as premise.
- `frames_before`: rows 0 .. 32 from R1's `all_adjacent_frame_order`,
  carried to the longer trace (`before_append`), then rows 32 .. n.
- the three table maps at row n's frame equal those at row 32's frame (both
  equal the full-trace maps, R1's `recover_current_table_eq_full`), so the
  chosen words equal R1's chosen words at row 32, which R1 proves equal to
  `wordsFromRun` of R1's run; that equals `wordsFromRun` of the 40-row run.
Model level. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FinalWords
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1
open RawCutProverCompiler (Prover RunView experiment)
open RawCutWordsFromView (frame frameFromView)
open BinMerkle32Path BinMerkle32Leaf BinMerkleTable BinMerkleLeafRecovery BinMerkleRecordedLog

abbrev params := SelectedTranscriptParams.params
abbrev Run40 (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State) : RunView :=
  eval H (experiment P (AspisRows40.Starts.verifier D d))
abbrev Run33 (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State) : RunView :=
  eval H (experiment P (RawCutProverCompiler.verifier D d))

/-! ## The 40-row run against R1's run -/

theorem split (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State) :
    (∃ tail, (Run40 D d P H).1 = (Run33 D d P H).1 ++ tail) ∧
      (Run40 D d P H).2.1 = (Run33 D d P H).2.1 := by
  unfold Run40 Run33
  rw [RawCutProverCompiler.experiment_eval, RawCutProverCompiler.experiment_eval,
    AspisRows40.Starts.verifier, RawCutProverCompiler.verifier, FS2.verifier_eval, FS2.verifier_eval]
  refine ⟨?_, rfl⟩
  dsimp only
  rw [show (AspisRows40.Protocol.protocol D).r = 33 + 7 from rfl, List.range_add,
    List.map_append, List.flatten_append, AspisRec40.CleanRun.chains_eq]
  exact ⟨_, by rw [List.append_assoc]; rfl⟩

theorem consistent40 (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State) : ∀ q ∈ (Run40 D d P H).1, q.2 = H q.1 :=
  FS.eval_consistent H _

theorem frame_read40 (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State) (i : Nat) (hi : i < 40) :
    Read (Run40 D d P H).1 (frame D H (Run40 D d P H).2.1.1 (Run40 D d P H).2.1.2 i) := by
  have h := AspisRec40.Frames.frame_read D (OracleDecisionFeasibilityCore.lift d) P H i hi
  dsimp only at h
  rw [AspisRec40.Frames.lift_verifier_fun] at h
  exact h

theorem verifier_read40 (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State) (a : Bytes)
    (ha : a ∈ (eval H (AspisRows40.Starts.verifier D d (Run40 D d P H).2.1.1
      (Run40 D d P H).2.1.2)).1.map Prod.fst) :
    Read (Run40 D d P H).1 a := by
  unfold Run40 at ha ⊢
  unfold Read
  rw [RawCutProverCompiler.experiment_eval] at ha ⊢
  simp only [List.map_append]
  exact List.mem_append.mpr (Or.inr ha)

/-- `Before` is kept when the trace is extended. -/
theorem before_append {I A : Type} [DecidableEq I] (H : I → A) (tr tail : List (I × A))
    (hcons : ∀ q ∈ tr ++ tail, q.2 = H q.1) (a b : I) (hb : Read tr b)
    (h : Before tr a b) : Before (tr ++ tail) a b := by
  have hcons' : ∀ q ∈ tr, q.2 = H q.1 := fun q hq => hcons q (List.mem_append_left _ hq)
  have e := TraceAppend.tableBefore_append emptyTable tr tail b hb
  have h1 := tableBefore_eq H (tr ++ tail) emptyTable b a hcons
  have h2 := tableBefore_eq H tr emptyTable b a hcons'
  rw [e, h2, if_pos h] at h1
  by_contra hn
  rw [if_neg hn] at h1
  simp [emptyTable] at h1

/-! ## Row shape and the next frame (copies of R1's `RWireRawCutLiteralNextFrame`) -/

theorem payload_of_valid {i : Nat} (hi0 : i ≠ 0) (m : LiteralTranscript.Message)
    (hm : LiteralTranscript.valid i m) : ∃ b, LiteralTranscript.erase m = .payload b := by
  cases i with
  | zero => exact (hi0 rfl).elim
  | succ n =>
      cases m with
      | initial root word => simp [LiteralTranscript.valid] at hm
      | payload b => exact ⟨b, rfl⟩
      | c2 b word => exact ⟨b, rfl⟩
      | second b word => exact ⟨b, rfl⟩

private theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (label : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map label s) = (firstCell s).map label := by
  cases s <;> rfl

private theorem payload_first_cell (i : Nat) (hi0 : i ≠ 0)
    (P : LiteralTranscript.Prefix) (payloadBytes : SelectedTranscriptParams.Message) :
    firstCell (LiteralTranscript.samp i P (.payload payloadBytes)) =
      some (UnifiedSampler.absorb SelectedTranscriptParams.params i
        (LiteralTranscript.erasePrefix P) payloadBytes) := by
  let p := SelectedTranscriptParams.params
  have hD : 5 ≤ p.D := by
    norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]
  change firstCell (UnifiedSampler.samp p hD i (LiteralTranscript.erasePrefix P)
    (.payload payloadBytes)) = some (UnifiedSampler.absorb p i
      (LiteralTranscript.erasePrefix P) payloadBytes)
  cases i with
  | zero => exact (hi0 rfl).elim
  | succ n =>
      by_cases h26 : n + 1 = 26
      · simp [UnifiedSampler.samp, h26, UnifiedSampler.absorb,
          DuplexSamplers.reseeded, FS2.firstCell]
      · by_cases h31 : n + 1 = 31
        · simp [UnifiedSampler.samp, h26, h31, UnifiedSampler.absorb,
            QuerySamplerBridge.sampler, FS2.firstCell]
        · simp [UnifiedSampler.samp, h26, h31, UnifiedSampler.absorb,
            DuplexSamplers.plain, FS2.firstCell]

theorem frame_eq_absorb (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    {i : Nat} (hi0 : i ≠ 0) (payloadBytes : SelectedTranscriptParams.Message)
    (hm : LiteralTranscript.erase (pf i) = .payload payloadBytes) :
    frame D H pub pf i =
      (UnifiedSampler.absorb SelectedTranscriptParams.params i
        (LiteralTranscript.erasePrefix
          ((LiteralByteProtocol.protocol D).transcript H pub pf i)) payloadBytes).toBytes := by
  unfold RawCutWordsFromView.frame
  change (firstCell (ProgramSamplerMap.map Addr.toBytes
      (LiteralTranscript.samp i
        ((LiteralByteProtocol.protocol D).transcript H pub pf i) (pf i)))).getD [] = _
  have hsampler : LiteralTranscript.samp i
      ((LiteralByteProtocol.protocol D).transcript H pub pf i) (pf i) =
      LiteralTranscript.samp i
        ((LiteralByteProtocol.protocol D).transcript H pub pf i) (.payload payloadBytes) := by
    unfold LiteralTranscript.samp
    rw [hm]
    simp [LiteralTranscript.erase]
  rw [firstCell_map, hsampler]
  simp [payload_first_cell, hi0]

/-- Copy of `next_frame_prefix` with the payload form as premise. -/
theorem next_prefix (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    {j : Nat} (hj0 : j ≠ 0) (hm : ∃ b, LiteralTranscript.erase (pf j) = .payload b) :
    (frame D H pub pf j).take 32 =
      bytes (UnifiedSampler.stateOf params
        (LiteralTranscript.erasePrefix
          ((LiteralByteProtocol.protocol D).transcript H pub pf j))) := by
  obtain ⟨payloadBytes, hbytes⟩ := hm
  rw [frame_eq_absorb D H pub pf hj0 payloadBytes hbytes]
  exact toBytes_absorbA SelectedTranscriptParams.params
    (UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol D).transcript H pub pf j)))
    (SelectedTranscriptParams.params.lbl j)
    (SelectedTranscriptParams.params.enc payloadBytes)
    (SelectedTranscriptParams.params.encLen payloadBytes)

/-- Copy of `ordinary_next_prefix_state` with the payload form as premise. -/
theorem next_state (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    {i : Nat} (hi0 : i ≠ 0) (hi26 : i ≠ 26) (hi31 : i ≠ 31)
    (hm : ∃ b, LiteralTranscript.erase (pf i) = .payload b) :
    UnifiedSampler.stateOf params
      (LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol D).transcript H pub pf (i + 1))) =
      H ((advanceA params (H (frame D H pub pf i))).toBytes) := by
  obtain ⟨payloadBytes, hbytes⟩ := hm
  let P := (LiteralByteProtocol.protocol D).transcript H pub pf i
  have hframe := frame_eq_absorb D H pub pf hi0 payloadBytes hbytes
  have hsuccessor := RawCutLiteralTranscriptSuccessor.actual_successor_state D H pub pf i
  have hchain : (LiteralByteProtocol.protocol D).chain H pub pf i =
      LiteralByteSampler.samp i P (pf i) := rfl
  have hbytesSampler : LiteralByteSampler.samp i P (pf i) =
      LiteralByteSampler.samp i P (.payload payloadBytes) := by
    apply congrArg (ProgramSamplerMap.map Addr.toBytes)
    unfold LiteralTranscript.samp
    rw [hbytes]
    rfl
  rw [hchain, hbytesSampler] at hsuccessor
  rw [RawCutLiteralStateSuccessor.ordinary_payload_state
    H P payloadBytes i hi0 hi26 hi31] at hsuccessor
  change UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol D).transcript H pub pf (i + 1))) =
    H ((advanceA SelectedTranscriptParams.params
      (H ((UnifiedSampler.absorb SelectedTranscriptParams.params i
        (LiteralTranscript.erasePrefix P) payloadBytes).toBytes))).toBytes) at hsuccessor
  rw [← hframe] at hsuccessor
  exact hsuccessor

/-- Copy of `ordinary_advance_read` for the 40-row verifier, `i < 40`. -/
theorem advance_read40 (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State)
    {i : Nat} (hi : i < 40) (hi0 : i ≠ 0) (hi26 : i ≠ 26) (hi31 : i ≠ 31)
    (hm : ∃ b, LiteralTranscript.erase ((Run40 D d P H).2.1.2 i) = .payload b) :
    Read (Run40 D d P H).1 ((advanceA params
      (H (frame D H (Run40 D d P H).2.1.1 (Run40 D d P H).2.1.2 i))).toBytes) := by
  let p := SelectedTranscriptParams.params
  let pub := (Run40 D d P H).2.1.1
  let pf := (Run40 D d P H).2.1.2
  let Pp := (LiteralByteProtocol.protocol D).transcript H pub pf i
  obtain ⟨payloadBytes, hbytes⟩ := hm
  have hframe := frame_eq_absorb D H pub pf hi0 payloadBytes hbytes
  let H' : FS2.Duplex.Addr SelectedTranscriptParams.L → State := fun a => H a.toBytes
  let a := UnifiedSampler.absorb p i (LiteralTranscript.erasePrefix Pp) payloadBytes
  let adv := advanceA p (H' a)
  have hD : 5 ≤ p.D := by
    norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]
  have htyped : LiteralTranscript.samp i Pp (pf i) =
      LiteralTranscript.samp i Pp (.payload payloadBytes) := by
    unfold LiteralTranscript.samp
    rw [hbytes]
    rfl
  have hbyte : LiteralByteSampler.samp i Pp (pf i) =
      LiteralByteSampler.samp i Pp (.payload payloadBytes) :=
    congrArg (ProgramSamplerMap.map Addr.toBytes) htyped
  have hbase : adv ∈
      (eval H' (LiteralTranscript.samp i Pp (.payload payloadBytes)).toProgram).1.map Prod.fst := by
    change adv ∈ (eval H' (UnifiedSampler.samp p hD i
      (LiteralTranscript.erasePrefix Pp) (.payload payloadBytes)).toProgram).1.map Prod.fst
    rw [UnifiedSampler.row_ordinary p hD i hi0 hi26 hi31
      (LiteralTranscript.erasePrefix Pp) payloadBytes]
    rw [DuplexSamplers.plain_eval]
    simp only [List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil]
    exact Or.inr (Or.inr (Or.inl rfl))
  have htraceBytes : adv.toBytes ∈
      (eval H (LiteralByteSampler.samp i Pp (.payload payloadBytes)).toProgram).1.map Prod.fst := by
    rw [LiteralByteSampler.eval_eq]
    simp only [AspisV8R19.OracleProgramOps.mapView, List.map_map, Function.comp_def]
    rcases List.mem_map.mp hbase with ⟨q, hpair, haddr⟩
    rcases q with ⟨addr, state⟩
    apply List.mem_map.mpr
    refine ⟨(addr, state), hpair, ?_⟩
    exact congrArg Addr.toBytes haddr
  have htrace : adv.toBytes ∈
      (eval H ((AspisRows40.Protocol.protocol D).chain H pub pf i).toProgram).1.map Prod.fst := by
    rw [AspisRows40.Protocol.chain_eq]
    have hchain : (LiteralByteProtocol.protocol D).chain H pub pf i =
        LiteralByteSampler.samp i Pp (pf i) := rfl
    rw [hchain, hbyte]
    exact htraceBytes
  have hverifier := FS2.verifier_reads (AspisRows40.Protocol.protocol D)
    (RawCutTranscriptRun.decisionOnBytes d) H pub pf i hi adv.toBytes htrace
  have hread : Read (Run40 D d P H).1 adv.toBytes :=
    verifier_read40 D d P H adv.toBytes hverifier
  have hadv : adv = advanceA p (H (frame D H pub pf i)) := by
    change advanceA p (H a.toBytes) = _
    rw [← hframe]
  rw [← hadv]
  exact hread

/-- Frames of rows i and i+1 (32 ≤ i < 39) are read in order on the 40-row run. -/
theorem adjacent40 (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State) (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable (Run40 D d P H).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable
      (Run40 D d P H).1)
    (i : Nat) (hlo : 32 ≤ i) (hi : i + 1 < 40)
    (hpi : ∃ b, LiteralTranscript.erase ((Run40 D d P H).2.1.2 i) = .payload b)
    (hpj : ∃ b, LiteralTranscript.erase ((Run40 D d P H).2.1.2 (i + 1)) = .payload b) :
    Before (Run40 D d P H).1
      (frame D H (Run40 D d P H).2.1.1 (Run40 D d P H).2.1.2 i)
      (frame D H (Run40 D d P H).2.1.1 (Run40 D d P H).2.1.2 (i + 1)) := by
  have hcons := consistent40 D d P H
  have hfi := frame_read40 D d P H i (by omega)
  have hfj := frame_read40 D d P H (i + 1) hi
  have hadv := advance_read40 D d P H (i := i) (by omega) (by omega) (by omega) (by omega) hpi
  have h1 := BinRawByteCollisionTargets.duplex_state_before_frame iv H _ Q hcons hQ hout
    _ _ hfi hadv (toBytes_advanceA params _)
  have hpre := next_prefix D H (Run40 D d P H).2.1.1 (Run40 D d P H).2.1.2 (j := i + 1)
    (by omega) hpj
  rw [next_state D H _ _ (i := i) (by omega) (by omega) (by omega) hpi] at hpre
  have h2 := BinRawByteCollisionTargets.duplex_state_before_frame iv H _ Q hcons hQ hout
    _ _ hadv hfj hpre
  exact before_trans _ h1 h2

/-- All adjacent frames of rows 0 .. 39 are read in order on the 40-row run. -/
theorem adjacent_all (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State) (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable (Run40 D d P H).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable
      (Run40 D d P H).1)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i ((Run40 D d P H).2.1.2 i))
    (hshape : AspisRec40.FinalShape.LatePayload (Run40 D d P H).2.1.2)
    (i : Nat) (hi : i + 1 < 40) :
    Before (Run40 D d P H).1
      (frame D H (Run40 D d P H).2.1.1 (Run40 D d P H).2.1.2 i)
      (frame D H (Run40 D d P H).2.1.1 (Run40 D d P H).2.1.2 (i + 1)) := by
  obtain ⟨⟨tail, ht⟩, hs⟩ := split D d P H
  by_cases h32 : i < 32
  · have hQR : firstReads emptyTable (Run33 D d P H).1 ≤ Q :=
      (TraceAppend.firstReads_le_append emptyTable _ tail).trans (by rw [← ht]; exact hQ)
    have houtR : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
        emptyTable (Run33 D d P H).1 := by
      intro h; apply hout; rw [ht]; exact TraceAppend.hitsBad_of_prefix _ _ _ _ h
    have hvalidR : ∀ i < 33, LiteralTranscript.valid i ((Run33 D d P H).2.1.2 i) := by
      rw [← hs]; exact hvalid
    have hR := RWireRawCutLiteralAllFrames.all_adjacent_frame_order D d P H (Run33 D d P H) rfl
      iv Q hQR houtR hvalidR i h32
    have hread : Read (Run33 D d P H).1 (frame D H (Run33 D d P H).2.1.1 (Run33 D d P H).2.1.2 (i + 1)) :=
      RawCutWordsFromView.frame_read D d P H (i + 1) (by omega)
    have hcons : ∀ q ∈ (Run33 D d P H).1 ++ tail, q.2 = H q.1 := by
      rw [← ht]; exact consistent40 D d P H
    have hb := before_append H _ tail hcons _ _ hread hR
    rw [← ht, ← hs] at hb
    exact hb
  · have hpay (j : Nat) (hj : 32 ≤ j) (hj40 : j < 40) :
        ∃ b, LiteralTranscript.erase ((Run40 D d P H).2.1.2 j) = .payload b := by
      by_cases h33 : j < 33
      · exact payload_of_valid (by omega) _ (hvalid j h33)
      · exact hshape j (by omega) hj40
    exact adjacent40 D d P H iv Q hQ hout i (by omega) hi (hpay i (by omega) (by omega))
      (hpay (i + 1) (by omega) hi)

theorem frames_before (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State) (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable (Run40 D d P H).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable
      (Run40 D d P H).1)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i ((Run40 D d P H).2.1.2 i))
    (hshape : AspisRec40.FinalShape.LatePayload (Run40 D d P H).2.1.2)
    (c : Nat) : ∀ m, c < m → m < 40 →
      Before (Run40 D d P H).1
        (frame D H (Run40 D d P H).2.1.1 (Run40 D d P H).2.1.2 c)
        (frame D H (Run40 D d P H).2.1.1 (Run40 D d P H).2.1.2 m) := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
      intro hcm hm
      have hstep := adjacent_all D d P H iv Q hQ hout hvalid hshape m hm
      by_cases hc : c = m
      · subst hc; exact hstep
      · exact before_trans _ (ih (by omega) (by omega)) hstep

/-! ## Words -/

theorem words_ext (x y : CanonicalCutEnrichedTranscript.Words)
    (h1 : x.c1 = y.c1) (h2 : x.c2 = y.c2) (h3 : x.final = y.final) : x = y := by
  cases x; cases y; simp_all

theorem words_of_recover (Tn T32 : Table Bytes State) (r1 r2 r3 : State)
    (h1 : ∀ tag width, (fun s => RWireRawByteTableWords.recoverFromTable Tn tag width s r1) =
      (fun s => RWireRawByteTableWords.recoverFromTable T32 tag width s r1))
    (h2 : ∀ tag width, (fun s => RWireRawByteTableWords.recoverFromTable Tn tag width s r2) =
      (fun s => RWireRawByteTableWords.recoverFromTable T32 tag width s r2))
    (h3 : ∀ tag width, (fun s => RWireRawByteTableWords.recoverFromTable Tn tag width s r3) =
      (fun s => RWireRawByteTableWords.recoverFromTable T32 tag width s r3)) :
    RawByteTableWordsBin.words Tn Tn Tn r1 r2 r3 = RawByteTableWordsBin.words T32 T32 T32 r1 r2 r3 := by
  have e1 : RawByteTableWordsBin.c1Map Tn r1 = RawByteTableWordsBin.c1Map T32 r1 := by
    funext q
    exact congrArg (Option.map Prod.fst) (congrFun (h1 _ _) _)
  have e2 : RawByteTableWordsBin.c2Map Tn r2 = RawByteTableWordsBin.c2Map T32 r2 := by
    funext q
    exact congrArg (Option.map Prod.fst) (congrFun (h2 _ _) _)
  have e3 : RawByteTableWordsBin.foldedMap Tn r3 = RawByteTableWordsBin.foldedMap T32 r3 := by
    funext q
    exact congrArg (Option.map Prod.fst) (congrFun (h3 _ _) _)
  unfold RawByteTableWordsBin.words
  rw [e1, e2, e3]

/-- Copy of `CleanRun.words_base_eq` for any prover and decision. -/
theorem words_run_eq (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State) :
    BinCompiledRunWordStability.wordsFromRun D (Run40 D d P H) =
      BinCompiledRunWordStability.wordsFromRun D (Run33 D d P H) := by
  obtain ⟨⟨tail, ht⟩, hs⟩ := split D d P H
  have hf (n : Nat) (hn : n < 33) :
      frameFromView D (Run40 D d P H) n = frameFromView D (Run33 D d P H) n := by
    have a : frameFromView D (Run40 D d P H) n =
        frame D H (Run40 D d P H).2.1.1 (Run40 D d P H).2.1.2 n := by
      have h := AspisRec40.Frames.frameFromView_eq D (OracleDecisionFeasibilityCore.lift d) P H n
        (by omega)
      dsimp only at h
      rw [AspisRec40.Frames.lift_verifier_fun] at h
      exact h
    have b : frameFromView D (Run33 D d P H) n =
        frame D H (Run33 D d P H).2.1.1 (Run33 D d P H).2.1.2 n :=
      RawCutWordsFromView.frameFromView_eq D d P H n (by omega)
    rw [a, b, hs]
  have hc (n : Nat) (hn : n < 33) :
      BinRawByteCutRecovery.cut (Run40 D d P H).1 (frameFromView D (Run33 D d P H) n) =
        BinRawByteCutRecovery.cut (Run33 D d P H).1 (frameFromView D (Run33 D d P H) n) := by
    rw [ht]
    apply OracleProgramRecording.cut_append_of_read
    rw [RawCutWordsFromView.frameFromView_eq D d P H n (by omega)]
    exact RawCutWordsFromView.frame_read D d P H n hn
  unfold BinCompiledRunWordStability.wordsFromRun
  rw [hf 0 (by decide), hf 2 (by decide), hf 30 (by decide)]
  unfold BinCanonicalCutWords.wordsFromRawCuts BinCanonicalCutWords.rawC1Map
    BinCanonicalCutWords.rawC2Map BinCanonicalCutWords.rawFoldedMap
  dsimp only
  rw [hc 0 (by decide), hc 2 (by decide), hc 30 (by decide)]

/-- W3: word choice for rows 33 to 39. Work-order statement plus `hshape`. -/
theorem constructed_components40 (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RunView)
    (hrun : run = eval H (experiment prover (AspisRows40.Starts.verifier decoder d)))
    (iv : State) (Q : Nat) (hQ : firstReads emptyTable run.1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable run.1)
    (hvalid : ∀ i < 33, LiteralTranscript.valid i (run.2.1.2 i))
    (hshape : AspisRec40.FinalShape.LatePayload run.2.1.2)
    (n : Nat) (hlo : 33 ≤ n) (hhi : n < 40)
    (r1 : State) (w1 : LiteralTranscript.C1Word)
    (b2 : LiteralTranscript.BytesMessage) (w2 : LiteralTranscript.C2Word) (r2 : State)
    (b30 : LiteralTranscript.BytesMessage) (w30 : LiteralTranscript.VWord)
    (v30 : OpeningRecordCodec.Payload .second)
    (h0 : run.2.1.2 0 = .initial r1 w1)
    (h2 : run.2.1.2 2 = .c2 b2 w2)
    (h30 : run.2.1.2 30 = .second b30 w30)
    (hp2 : SemanticRecordCodec.decode ⟨2,by decide⟩ b2.val = some ⟨.c2Root r2,by rfl⟩)
    (hp30 : OpeningRecordCodec.decode .second b30.val = some v30) :
    let frame := RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 n
    let w := LiteralTableWordChoiceBin.choose frame (tableBefore emptyTable run.1 frame)
      (LiteralTranscript.erasePrefix ((AspisRows40.Protocol.protocol decoder).transcript H
        run.2.1.1 run.2.1.2 n))
      (LiteralTranscript.erase (run.2.1.2 n))
    w = BinCompiledRunWordStability.wordsFromRun decoder run := by
  subst hrun
  dsimp only
  have hcons := consistent40 decoder d prover H
  obtain ⟨⟨tail, ht⟩, hs⟩ := split decoder d prover H
  have hord := frames_before decoder d prover H iv Q hQ hout hvalid hshape
  -- R1's premises on R1's run
  have hQR : firstReads emptyTable (Run33 decoder d prover H).1 ≤ Q :=
    (TraceAppend.firstReads_le_append emptyTable _ tail).trans (by rw [← ht]; exact hQ)
  have houtR : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable (Run33 decoder d prover H).1 := by
    intro h; apply hout; rw [ht]; exact TraceAppend.hitsBad_of_prefix _ _ _ _ h
  have hvalidR : ∀ i < 33, LiteralTranscript.valid i ((Run33 decoder d prover H).2.1.2 i) := by
    rw [← hs]; exact hvalid
  have h0R : (Run33 decoder d prover H).2.1.2 0 = .initial r1 w1 := by rw [← hs]; exact h0
  have h2R : (Run33 decoder d prover H).2.1.2 2 = .c2 b2 w2 := by rw [← hs]; exact h2
  have h30R : (Run33 decoder d prover H).2.1.2 30 = .second b30 w30 := by rw [← hs]; exact h30
  -- R1 at row 32: the chosen words are the words of R1's run
  have hR := RWireLiteralTableChoiceWords.constructed_components decoder d prover H
    (Run33 decoder d prover H) rfl iv Q hQR houtR hvalidR 32 (by decide)
    r1 w1 b2 w2 r2 b30 w30 v30 h0R h2R h30R hp2 hp30
  dsimp only at hR
  have hw32 : RWireLiteralTableChoiceWords.atRun decoder H (Run33 decoder d prover H) 32 =
      BinCompiledRunWordStability.wordsFromRun decoder (Run33 decoder d prover H) :=
    words_ext _ _ hR.1 (hR.2.1 (by decide)) (hR.2.2 (by decide))
  have hW : BinCompiledRunWordStability.wordsFromRun decoder (Run40 decoder d prover H) =
      BinCompiledRunWordStability.wordsFromRun decoder (Run33 decoder d prover H) :=
    words_run_eq decoder d prover H
  -- the maps at row n's frame are the maps at row 32's frame
  have hread (i : Nat) (hi : i < 40) := frame_read40 decoder d prover H i hi
  have hread32 : Read (Run33 decoder d prover H).1
      (frame decoder H (Run40 decoder d prover H).2.1.1 (Run40 decoder d prover H).2.1.2 32) := by
    have h := RawCutWordsFromView.frame_read decoder d prover H 32 (by decide)
    dsimp only at h
    rw [hs]
    exact h
  have hT32 : tableBefore emptyTable (Run40 decoder d prover H).1
        (frame decoder H (Run40 decoder d prover H).2.1.1 (Run40 decoder d prover H).2.1.2 32) =
      tableBefore emptyTable (Run33 decoder d prover H).1
        (frame decoder H (Run40 decoder d prover H).2.1.1 (Run40 decoder d prover H).2.1.2 32) := by
    rw [ht]
    exact TraceAppend.tableBefore_append _ _ _ _ hread32
  have hrec (j : Fin 5) (c : Nat) (hc : c < 32) (root : State)
      (hpred : BinRawByteCollisionTargets.pred j
        (frame decoder H (Run40 decoder d prover H).2.1.1 (Run40 decoder d prover H).2.1.2 c) =
          some root) :
      ∀ tag width,
        (fun s => RWireRawByteTableWords.recoverFromTable
          (tableBefore emptyTable (Run40 decoder d prover H).1
            (frame decoder H (Run40 decoder d prover H).2.1.1 (Run40 decoder d prover H).2.1.2 n))
          tag width s root) =
        (fun s => RWireRawByteTableWords.recoverFromTable
          (tableBefore emptyTable (Run33 decoder d prover H).1
            (frame decoder H (Run40 decoder d prover H).2.1.1 (Run40 decoder d prover H).2.1.2 32))
          tag width s root) := by
    intro tag width
    have a := RWireRawCutLaterTableLiteralWords.recover_current_table_eq_full iv H _ Q hcons hQ hout
      _ _ root tag width j (hread n hhi) (hread c (by omega)) hpred
      (Or.inl (hord c n (by omega) hhi))
    have b := RWireRawCutLaterTableLiteralWords.recover_current_table_eq_full iv H _ Q hcons hQ hout
      _ _ root tag width j (hread 32 (by decide)) (hread c (by omega)) hpred
      (Or.inl (hord c 32 (by omega) (by decide)))
    rw [a, ← b, hT32]
  have hp0 := RWireConstructedWords.initial_root decoder H (Run40 decoder d prover H).2.1.1
    (Run40 decoder d prover H).2.1.2 r1 w1 h0
  have hp2' := RWireConstructedWords.c2_root decoder H (Run40 decoder d prover H).2.1.1
    (Run40 decoder d prover H).2.1.2 b2 w2 r2 h2 hp2
  have hp30' := RWireConstructedWords.second_root decoder H (Run40 decoder d prover H).2.1.1
    (Run40 decoder d prover H).2.1.2 b30 w30 v30 h30 hp30
  rw [hW, ← hw32]
  unfold RWireLiteralTableChoiceWords.atRun LiteralTableWordChoiceBin.choose
  rw [← hs, AspisRows40.Protocol.transcript_eq,
    LiteralTableChoiceRun.c1_root decoder H (Run40 decoder d prover H).2.1.1 (Run40 decoder d prover H).2.1.2 n r1 w1 h0,
    LiteralTableChoiceRun.c2_root decoder H (Run40 decoder d prover H).2.1.1 (Run40 decoder d prover H).2.1.2 n (by omega) b2 w2 r2 h2 hp2,
    LiteralTableChoiceRun.final_root decoder H (Run40 decoder d prover H).2.1.1 (Run40 decoder d prover H).2.1.2 n (by omega) b30 w30 v30 h30 hp30,
    LiteralTableChoiceRun.c1_root decoder H (Run40 decoder d prover H).2.1.1 (Run40 decoder d prover H).2.1.2 32 r1 w1 h0,
    LiteralTableChoiceRun.c2_root decoder H (Run40 decoder d prover H).2.1.1 (Run40 decoder d prover H).2.1.2 32 (by decide) b2 w2 r2 h2 hp2,
    LiteralTableChoiceRun.final_root decoder H (Run40 decoder d prover H).2.1.1 (Run40 decoder d prover H).2.1.2 32 (by decide) b30 w30 v30 h30 hp30]
  exact words_of_recover _ _ _ _ _ (hrec 2 0 (by decide) r1 hp0) (hrec 2 2 (by decide) r2 hp2')
    (hrec 3 30 (by decide) v30.1 hp30')

#print axioms split
#print axioms frame_read40
#print axioms before_append
#print axioms next_prefix
#print axioms next_state
#print axioms advance_read40
#print axioms adjacent40
#print axioms adjacent_all
#print axioms frames_before
#print axioms words_of_recover
#print axioms words_run_eq
#print axioms constructed_components40

end AspisRec40.FinalWords
end
