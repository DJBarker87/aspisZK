import RawCutLiteralStateSuccessor
import RawCutLiteralTranscriptSuccessor
import RWireRawCutLiteralSamplerOrder
import RawCutWordsFromView
import BinRawByteCollisionTargets

/-! Exact prefix and transition helpers for the next literal frame. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawCutLiteralNextFrame

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.LiteralTranscript
open AspisR1.UnifiedSampler
open AspisR1.RawCutProverCompiler
open AspisR1.RawCutWordsFromView
open AspisR1.BinRawByteCollisionTargets

private theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (label : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map label s) = (firstCell s).map label := by
  cases s <;> rfl

private theorem erased_valid_payload {i : Nat} (hi0 : i ≠ 0)
    (m : LiteralTranscript.Message) (hm : LiteralTranscript.valid i m) :
    ∃ payloadBytes, LiteralTranscript.erase m = .payload payloadBytes := by
  cases i with
  | zero => exact (hi0 rfl).elim
  | succ n =>
      cases m with
      | initial root word => simp [LiteralTranscript.valid] at hm
      | payload payloadBytes => exact ⟨payloadBytes, rfl⟩
      | c2 payloadBytes word => exact ⟨payloadBytes, rfl⟩
      | second payloadBytes word => exact ⟨payloadBytes, rfl⟩

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

private theorem frame_eq_absorb_of_erased_payload
    (decoder : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    {i : Nat} (hi0 : i ≠ 0) (payloadBytes : SelectedTranscriptParams.Message)
    (hm : LiteralTranscript.erase (pf i) = .payload payloadBytes) :
    RawCutWordsFromView.frame decoder H pub pf i =
      (UnifiedSampler.absorb SelectedTranscriptParams.params i
        (LiteralTranscript.erasePrefix
          ((LiteralByteProtocol.protocol decoder).transcript H pub pf i)) payloadBytes).toBytes := by
  unfold RawCutWordsFromView.frame
  change (firstCell (ProgramSamplerMap.map Addr.toBytes
      (LiteralTranscript.samp i
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf i) (pf i)))).getD [] = _
  have hsampler : LiteralTranscript.samp i
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf i) (pf i) =
      LiteralTranscript.samp i
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf i) (.payload payloadBytes) := by
    unfold LiteralTranscript.samp
    rw [hm]
    simp [LiteralTranscript.erase]
  rw [firstCell_map, hsampler]
  simp [payload_first_cell, hi0]

/-- A valid noninitial literal frame starts with the state represented by the
transcript prefix immediately before it. -/
theorem next_frame_prefix
    (decoder : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    {j : Nat} (hj : j < 33) (hj0 : j ≠ 0)
    (hm : LiteralTranscript.valid j (pf j)) :
    (RawCutWordsFromView.frame decoder H pub pf j).take 32 =
      bytes (UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix
          ((LiteralByteProtocol.protocol decoder).transcript H pub pf j))) := by
  obtain ⟨payloadBytes, hbytes⟩ := erased_valid_payload hj0 _ hm
  rw [frame_eq_absorb_of_erased_payload decoder H pub pf hj0 payloadBytes hbytes]
  exact toBytes_absorbA SelectedTranscriptParams.params
    (UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf j)))
    (SelectedTranscriptParams.params.lbl j)
    (SelectedTranscriptParams.params.enc payloadBytes)
    (SelectedTranscriptParams.params.encLen payloadBytes)

/-- The actual ordinary sampler trace includes its advance input, and the
verifier-read theorem transports that input to the full experiment trace. -/
theorem ordinary_advance_read
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RunView)
    (hrun : run = eval H (experiment prover (verifier decoder d)))
    {i : Nat} (hi : i < 33) (hi0 : i ≠ 0) (hi26 : i ≠ 26) (hi31 : i ≠ 31)
    (hm : LiteralTranscript.valid i (run.2.1.2 i)) :
    Read run.1 ((advanceA SelectedTranscriptParams.params
      (H (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 i))).toBytes) := by
  let p := SelectedTranscriptParams.params
  let pub := run.2.1.1
  let pf := run.2.1.2
  let P := (LiteralByteProtocol.protocol decoder).transcript H pub pf i
  obtain ⟨payloadBytes, hbytes⟩ := erased_valid_payload hi0 _ hm
  have hframe := frame_eq_absorb_of_erased_payload decoder H pub pf hi0 payloadBytes hbytes
  let H' : FS2.Duplex.Addr SelectedTranscriptParams.L → State := fun a => H a.toBytes
  let a := UnifiedSampler.absorb p i (LiteralTranscript.erasePrefix P) payloadBytes
  let adv := advanceA p (H' a)
  have hD : 5 ≤ p.D := by
    norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]
  have htyped : LiteralTranscript.samp i P (pf i) =
      LiteralTranscript.samp i P (.payload payloadBytes) := by
    unfold LiteralTranscript.samp
    rw [hbytes]
    rfl
  have hbyte : LiteralByteSampler.samp i P (pf i) =
      LiteralByteSampler.samp i P (.payload payloadBytes) :=
    congrArg (ProgramSamplerMap.map Addr.toBytes) htyped
  have hbase : adv ∈
      (eval H' (LiteralTranscript.samp i P (.payload payloadBytes)).toProgram).1.map Prod.fst := by
    change adv ∈ (eval H' (UnifiedSampler.samp p hD i
      (LiteralTranscript.erasePrefix P) (.payload payloadBytes)).toProgram).1.map Prod.fst
    rw [UnifiedSampler.row_ordinary p hD i hi0 hi26 hi31
      (LiteralTranscript.erasePrefix P) payloadBytes]
    rw [DuplexSamplers.plain_eval]
    simp only [Prod.fst, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil]
    exact Or.inr (Or.inr (Or.inl rfl))
  have htraceBytes : adv.toBytes ∈
      (eval H (LiteralByteSampler.samp i P (.payload payloadBytes)).toProgram).1.map Prod.fst := by
    rw [LiteralByteSampler.eval_eq]
    simp only [AspisV8R19.OracleProgramOps.mapView, List.map_map, Function.comp_def]
    rcases List.mem_map.mp hbase with ⟨q, hpair, haddr⟩
    rcases q with ⟨addr, state⟩
    apply List.mem_map.mpr
    refine ⟨(addr, state), hpair, ?_⟩
    exact congrArg Addr.toBytes haddr
  have htrace : adv.toBytes ∈
      (eval H ((LiteralByteProtocol.protocol decoder).chain H pub pf i).toProgram).1.map Prod.fst := by
    have hchain : (LiteralByteProtocol.protocol decoder).chain H pub pf i =
        LiteralByteSampler.samp i P (pf i) := rfl
    rw [hchain, hbyte]
    exact htraceBytes
  have hverifier := FS2.verifier_reads (LiteralByteProtocol.protocol decoder)
    (RawCutTranscriptRun.decisionOnBytes d) H pub pf i hi adv.toBytes htrace
  have hpairs : ∃ state,
      (adv.toBytes, state) ∈
        (eval H (FS2.verifier (LiteralByteProtocol.protocol decoder)
          (RawCutTranscriptRun.decisionOnBytes d) pub pf)).1 := by
    rcases List.mem_map.mp hverifier with ⟨q, hq, ha⟩
    rcases q with ⟨addr, state⟩
    have haddr : addr = adv.toBytes := ha
    subst addr
    exact ⟨state, hq⟩
  have hreadActual := RawCutWordsFromView.verifier_reads_in_experiment
    decoder d prover H adv.toBytes (by
      simpa [RawCutProverCompiler.verifier, hrun, pub, pf] using hpairs)
  have hread : Read run.1 adv.toBytes := by
    change adv.toBytes ∈ run.1.map Prod.fst
    simpa [hrun] using hreadActual
  have hadv : adv = advanceA p (H (RawCutWordsFromView.frame decoder H pub pf i)) := by
    change advanceA p (H a.toBytes) = _
    rw [← hframe]
  rw [← hadv]
  exact hread

/-- At a valid ordinary payload row, the next transcript prefix records
exactly the oracle answer at that row's advance address. -/
theorem ordinary_next_prefix_state
    (decoder : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    {i : Nat} (hi0 : i ≠ 0) (hi26 : i ≠ 26) (hi31 : i ≠ 31)
    (hm : LiteralTranscript.valid i (pf i)) :
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf (i + 1))) =
      H ((advanceA SelectedTranscriptParams.params
        (H (RawCutWordsFromView.frame decoder H pub pf i))).toBytes) := by
  obtain ⟨payloadBytes, hbytes⟩ := erased_valid_payload hi0 _ hm
  let P := (LiteralByteProtocol.protocol decoder).transcript H pub pf i
  have hframe := frame_eq_absorb_of_erased_payload decoder H pub pf hi0 payloadBytes hbytes
  have hsuccessor := RawCutLiteralTranscriptSuccessor.actual_successor_state
    decoder H pub pf i
  have hchain : (LiteralByteProtocol.protocol decoder).chain H pub pf i =
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
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf (i + 1))) =
    H ((advanceA SelectedTranscriptParams.params
      (H ((UnifiedSampler.absorb SelectedTranscriptParams.params i
        (LiteralTranscript.erasePrefix P) payloadBytes).toBytes))).toBytes) at hsuccessor
  rw [← hframe] at hsuccessor
  exact hsuccessor

/-- If the state stored by row i is the oracle answer at address a, then the
next valid noninitial literal frame follows a in the actual no-collision
trace. -/
theorem state_address_before_next_frame
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RunView)
    (hrun : run = eval H (experiment prover (verifier decoder d)))
    (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable run.1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable run.1)
    {j : Nat} (hj : j < 33) (hj0 : j ≠ 0)
    (hm : LiteralTranscript.valid j (run.2.1.2 j))
    (a : FS2.Duplex.Addr SelectedTranscriptParams.L)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol decoder).transcript H run.2.1.1 run.2.1.2 j)) = H a.toBytes)
    (hreadA : Read run.1 a.toBytes) :
    Before run.1 a.toBytes
      (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 j) := by
  have hreadFrame : Read run.1
      (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 j) := by
    have h := RawCutWordsFromView.frame_read decoder d prover H j hj
    simpa [hrun] using h
  have hprefix := next_frame_prefix decoder H run.2.1.1 run.2.1.2 hj hj0 hm
  rw [hstate] at hprefix
  exact BinRawByteCollisionTargets.duplex_state_before_frame iv H run.1 Q
    (by rw [hrun]; exact FS.eval_consistent H _)
    hQ hout _ _ hreadA hreadFrame hprefix

/-- The preceding frame and following valid frame are ordered when the
actual sampler’s returned state is the answer at the supplied address. -/
theorem adjacent_frame_order_of_sampler_state
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RunView)
    (hrun : run = eval H (experiment prover (verifier decoder d)))
    (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable run.1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable run.1)
    {i : Nat} (hi : i + 1 < 33)
    (hiValid : LiteralTranscript.valid i (run.2.1.2 i))
    (hjValid : LiteralTranscript.valid (i + 1) (run.2.1.2 (i + 1)))
    (a : FS2.Duplex.Addr SelectedTranscriptParams.L)
    (hprev : Before run.1
      (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 i) a.toBytes)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol decoder).transcript H run.2.1.1 run.2.1.2 (i + 1))) = H a.toBytes)
    (hreadA : Read run.1 a.toBytes) :
    Before run.1
      (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 i)
      (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 (i + 1)) := by
  have hnext := state_address_before_next_frame decoder d prover H run hrun iv Q
    hQ hout (j := i + 1) (by omega) (by omega) hjValid a hstate hreadA
  exact before_trans run.1 hprev hnext

#print axioms next_frame_prefix
#print axioms state_address_before_next_frame
#print axioms adjacent_frame_order_of_sampler_state

#print axioms firstCell_map
#print axioms erased_valid_payload
#print axioms payload_first_cell
#print axioms frame_eq_absorb_of_erased_payload
#print axioms ordinary_advance_read
#print axioms ordinary_next_prefix_state
end AspisR1.RWireRawCutLiteralNextFrame
end
