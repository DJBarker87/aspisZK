import RawCutWordsFromView
import BinRawByteCollisionTargets
import R1UnifiedSampler
import R1DuplexSamplers
import R1QuerySamplerBridge
import R1SelectedTranscriptParams

/-! A row-local first-read ordering fact for the literal sampler. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawCutLiteralSamplerOrder

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.LiteralTranscript
open AspisR1.UnifiedSampler
open AspisR1.DuplexSamplers
open AspisR1.QuerySamplerBridge
open AspisR1.RawCutWordsFromView
open AspisR1.BinRawByteCollisionTargets
open AspisR1.RawCutProverCompiler

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

private theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (label : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map label s) = (firstCell s).map label := by
  cases s <;> rfl

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

/-- For a valid noninitial row, the first absorbing frame is before that row's
advance input in the actual experiment trace. -/
theorem ordinary_frame_before_advance
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RawCutProverCompiler.RunView)
    (hrun : run = eval H (experiment prover (verifier decoder d)))
    (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable run.1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable run.1)
    {i : Nat} (hi : i < 33) (hi0 : i ≠ 0)
    (hm : LiteralTranscript.valid i (run.2.1.2 i)) :
    Before run.1
      (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 i)
      (advanceA SelectedTranscriptParams.params
        (H (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 i))).toBytes := by
  let p := SelectedTranscriptParams.params
  let pub := run.2.1.1
  let pf := run.2.1.2
  let P := (LiteralByteProtocol.protocol decoder).transcript H pub pf i
  obtain ⟨payloadBytes, hbytes⟩ := erased_valid_payload hi0 _ hm
  have hframe := frame_eq_absorb_of_erased_payload decoder H pub pf hi0 payloadBytes hbytes
  have hreadFrame : Read run.1 (RawCutWordsFromView.frame decoder H pub pf i) := by
    have h := RawCutWordsFromView.frame_read decoder d prover H i hi
    simpa [hrun, pub, pf] using h
  let H' : FS2.Duplex.Addr SelectedTranscriptParams.L → State := fun a => H a.toBytes
  let a := UnifiedSampler.absorb p i (LiteralTranscript.erasePrefix P) payloadBytes
  let adv := advanceA p (H' a)
  have hadv : adv = advanceA p (H (RawCutWordsFromView.frame decoder H pub pf i)) := by
    change advanceA p (H a.toBytes) = _
    rw [← hframe]
  have hchain : (LiteralByteProtocol.protocol decoder).chain H pub pf i =
      LiteralByteSampler.samp i P (pf i) := rfl
  have htypedSampler : LiteralTranscript.samp i P (pf i) =
      LiteralTranscript.samp i P (.payload payloadBytes) := by
    unfold LiteralTranscript.samp
    rw [hbytes]
    simp [LiteralTranscript.erase]
  have hsamp : LiteralByteSampler.samp i P (pf i) =
      LiteralByteSampler.samp i P (.payload payloadBytes) := by
    exact congrArg (ProgramSamplerMap.map Addr.toBytes) htypedSampler
  have hD : 5 ≤ p.D := by
    norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]
  have hbase : adv ∈
      (eval H' (LiteralTranscript.samp i P (.payload payloadBytes)).toProgram).1.map Prod.fst := by
    change adv ∈ (eval H' (UnifiedSampler.samp p hD i
      (LiteralTranscript.erasePrefix P) (.payload payloadBytes)).toProgram).1.map Prod.fst
    by_cases h26 : i = 26
    · subst i
      rw [UnifiedSampler.row_reseed p hD (LiteralTranscript.erasePrefix P) payloadBytes]
      simp [DuplexSamplers.reseeded_eval, adv, a, H']
    · by_cases h31 : i = 31
      · subst i
        rw [UnifiedSampler.row_query p hD (LiteralTranscript.erasePrefix P) payloadBytes]
        have hq := QuerySamplerBridge.reads_pairs
          (p := p) (H := H') (C := LiteralTranscript.Challenge)
          a UnifiedSampler.liftQuery 0 (by decide)
        simpa [QuerySamplerBridge.sampler, QuerySampler.state, adv, H'] using hq.2
      · rw [UnifiedSampler.row_ordinary p hD i hi0 h26 h31
          (LiteralTranscript.erasePrefix P) payloadBytes]
        rw [DuplexSamplers.plain_eval]
        simp only [Prod.fst, List.map_cons, List.map_nil,
          List.mem_cons, List.not_mem_nil]
        exact Or.inr (Or.inr (Or.inl rfl))
  have hmap := congrArg (fun z => z.1.map Prod.fst)
    (LiteralByteSampler.eval_eq H i P (.payload payloadBytes))
  have htraceBytes : adv.toBytes ∈
      (eval H (LiteralByteSampler.samp i P (.payload payloadBytes)).toProgram).1.map Prod.fst := by
    rw [LiteralByteSampler.eval_eq]
    simp only [AspisV8R19.OracleProgramOps.mapView, List.map_map, Function.comp_def]
    rcases List.mem_map.mp hbase with ⟨q, hpair, haddr⟩
    rcases q with ⟨addr, state⟩
    apply List.mem_map.mpr
    refine ⟨(addr, state), hpair, ?_⟩
    exact congrArg Addr.toBytes haddr
  have htraceAdv : adv.toBytes ∈
      (eval H ((LiteralByteProtocol.protocol decoder).chain H pub pf i).toProgram).1.map Prod.fst := by
    rw [hchain, hsamp]
    exact htraceBytes
  have hreadAdv : Read run.1
      (advanceA p (H (RawCutWordsFromView.frame decoder H pub pf i))).toBytes := by
    have hread : Read run.1 adv.toBytes := by
      have htraceActual : adv.toBytes ∈
          (eval H ((LiteralByteProtocol.protocol decoder).chain H
            (eval H (experiment prover (verifier decoder d))).2.1.1
            (eval H (experiment prover (verifier decoder d))).2.1.2 i).toProgram).1.map Prod.fst := by
        simpa [hrun, pub, pf] using htraceAdv
      have hverifier := FS2.verifier_reads (LiteralByteProtocol.protocol decoder)
        (RawCutTranscriptRun.decisionOnBytes d) H
        (eval H (experiment prover (verifier decoder d))).2.1.1
        (eval H (experiment prover (verifier decoder d))).2.1.2 i hi adv.toBytes htraceActual
      have hreadActual := RawCutWordsFromView.verifier_reads_in_experiment decoder d prover H
        adv.toBytes (by
          simpa [RawCutProverCompiler.verifier] using hverifier)
      simpa [hrun, FS2.Duplex.Read] using hreadActual
    rw [← hadv]
    exact hread
  have hpre : (advanceA p (H (RawCutWordsFromView.frame decoder H pub pf i))).toBytes.take 32 =
      bytes (H (RawCutWordsFromView.frame decoder H pub pf i)) := by
    exact toBytes_advanceA p (H (RawCutWordsFromView.frame decoder H pub pf i))
  exact BinRawByteCollisionTargets.duplex_state_before_frame iv H run.1 Q
    (by rw [hrun]; exact FS.eval_consistent H _)
    hQ hout _ _ hreadFrame hreadAdv hpre

#print axioms ordinary_frame_before_advance

#print axioms erased_valid_payload
#print axioms payload_first_cell
#print axioms firstCell_map
#print axioms frame_eq_absorb_of_erased_payload
end AspisR1.RWireRawCutLiteralSamplerOrder
end
