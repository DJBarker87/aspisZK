import RWireRawCutLiteralNextFrame
import RawCutLiteralStateSuccessor
import RawCutLiteralTranscriptSuccessor
import RWireRawCutLiteralSamplerOrder
import RawCutWordsFromView
import RawCutProverCompiler
import BinRawByteCollisionTargets
import R1UnifiedSampler
import R1DuplexSamplers
import R1LiteralByteProtocol
import R1LiteralByteSampler
import R1OpeningReseedFrame

set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawCutLiteralReseedOrder

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.LiteralTranscript
open AspisR1.UnifiedSampler
open AspisR1.DuplexSamplers
open AspisR1.RawCutWordsFromView
open AspisR1.RawCutProverCompiler
open AspisR1.BinRawByteCollisionTargets

private theorem erased_valid_payload26 (m : LiteralTranscript.Message)
    (hm : LiteralTranscript.valid 26 m) :
    ∃ bytes, LiteralTranscript.erase m = .payload bytes := by
  cases m with
  | initial root word => simp [LiteralTranscript.valid] at hm
  | payload bytes => exact ⟨bytes, rfl⟩
  | c2 bytes word => exact ⟨bytes, rfl⟩
  | second bytes word => exact ⟨bytes, rfl⟩

private theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (label : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map label s) = (firstCell s).map label := by
  cases s <;> rfl

private theorem frame_eq_absorb26
    (decoder : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (payloadBytes : SelectedTranscriptParams.Message)
    (hm : LiteralTranscript.erase (pf 26) = .payload payloadBytes) :
    RawCutWordsFromView.frame decoder H pub pf 26 =
      (UnifiedSampler.absorb SelectedTranscriptParams.params 26
        (LiteralTranscript.erasePrefix
          ((LiteralByteProtocol.protocol decoder).transcript H pub pf 26))
        payloadBytes).toBytes := by
  unfold RawCutWordsFromView.frame
  change (firstCell (ProgramSamplerMap.map Addr.toBytes
      (LiteralTranscript.samp 26
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf 26)
        (pf 26)))).getD [] = _
  have hsampler : LiteralTranscript.samp 26
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 26) (pf 26) =
      LiteralTranscript.samp 26
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf 26)
        (.payload payloadBytes) := by
    unfold LiteralTranscript.samp
    rw [hm]
    simp [LiteralTranscript.erase]
  have hD : 5 ≤ SelectedTranscriptParams.params.D := by
    norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D]
  have hfirst : firstCell (LiteralTranscript.samp 26
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 26)
      (.payload payloadBytes)) = some
      (UnifiedSampler.absorb SelectedTranscriptParams.params 26
        (LiteralTranscript.erasePrefix
          ((LiteralByteProtocol.protocol decoder).transcript H pub pf 26))
        payloadBytes) := by
    change firstCell (UnifiedSampler.samp SelectedTranscriptParams.params hD 26
      (LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf 26))
      (.payload payloadBytes)) = _
    rw [UnifiedSampler.row_reseed]
    simp [DuplexSamplers.reseeded, FS2.firstCell]
  rw [firstCell_map, hsampler, hfirst]
  rfl

private theorem reseed_read_pair
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RawCutProverCompiler.RunView)
    (hrun : run = eval H (experiment prover (verifier decoder d)))
    (payloadBytes : SelectedTranscriptParams.Message)
    (hbytes : LiteralTranscript.erase (run.2.1.2 26) = .payload payloadBytes) :
    let P := (LiteralByteProtocol.protocol decoder).transcript H run.2.1.1 run.2.1.2 26
    let p := SelectedTranscriptParams.params
    let H' : FS2.Duplex.Addr SelectedTranscriptParams.L → State := fun a => H a.toBytes
    let a := UnifiedSampler.absorb p 26 (LiteralTranscript.erasePrefix P) payloadBytes
    let adv := advanceA p (H' a)
    let reseed := OpeningReseedFrame.addr (L := SelectedTranscriptParams.L)
      (LiteralTranscript.erasePrefix P).statement.tag (by norm_num [SelectedTranscriptParams.L]) (H' adv)
    Read run.1 adv.toBytes ∧ Read run.1 reseed.toBytes := by
  classical
  let p := SelectedTranscriptParams.params
  let pub := run.2.1.1
  let pf := run.2.1.2
  let P := (LiteralByteProtocol.protocol decoder).transcript H pub pf 26
  let H' : FS2.Duplex.Addr SelectedTranscriptParams.L → State := fun a => H a.toBytes
  let a := UnifiedSampler.absorb p 26 (LiteralTranscript.erasePrefix P) payloadBytes
  let adv := advanceA p (H' a)
  let reseed := OpeningReseedFrame.addr (L := SelectedTranscriptParams.L)
    (LiteralTranscript.erasePrefix P).statement.tag (by norm_num [SelectedTranscriptParams.L]) (H' adv)
  have hD : 5 ≤ p.D := by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]
  have htyped : LiteralTranscript.samp 26 P (pf 26) = LiteralTranscript.samp 26 P (.payload payloadBytes) := by
    unfold LiteralTranscript.samp
    rw [hbytes]
    rfl
  have hbytesSampler : LiteralByteSampler.samp 26 P (pf 26) = LiteralByteSampler.samp 26 P (.payload payloadBytes) :=
    congrArg (ProgramSamplerMap.map Addr.toBytes) htyped
  have hbase (u : Addr SelectedTranscriptParams.L)
      (hu : u = adv ∨ u = reseed) :
      u ∈ (eval H' (LiteralTranscript.samp 26 P (.payload payloadBytes)).toProgram).1.map Prod.fst := by
    change u ∈ (eval H' (UnifiedSampler.samp p hD 26
      (LiteralTranscript.erasePrefix P) (.payload payloadBytes)).toProgram).1.map Prod.fst
    rw [UnifiedSampler.row_reseed p hD (LiteralTranscript.erasePrefix P) payloadBytes]
    rw [DuplexSamplers.reseeded_eval]
    change u ∈ [a, squeezeA p (H' a), adv,
      OpeningReseedFrame.addr (LiteralTranscript.erasePrefix P).statement.tag
        (by have := (LiteralTranscript.erasePrefix P).statement.initFits; omega) (H' adv)]
    rcases hu with rfl | rfl
    · simp [adv]
    · simp [reseed, adv]
  have hconvert (u : Addr SelectedTranscriptParams.L)
      (hu : u ∈ (eval H' (LiteralTranscript.samp 26 P (.payload payloadBytes)).toProgram).1.map Prod.fst) :
      u.toBytes ∈ (eval H (LiteralByteSampler.samp 26 P (.payload payloadBytes)).toProgram).1.map Prod.fst := by
    rw [LiteralByteSampler.eval_eq]
    simp only [AspisV8R19.OracleProgramOps.mapView, List.map_map, Function.comp_def]
    rcases List.mem_map.mp hu with ⟨q, hpair, haddr⟩
    rcases q with ⟨addr, state⟩
    apply List.mem_map.mpr
    refine ⟨(addr, state), hpair, ?_⟩
    exact congrArg Addr.toBytes haddr
  have htrace (u : Addr SelectedTranscriptParams.L) (hu : u = adv ∨ u = reseed) :
      u.toBytes ∈ (eval H ((LiteralByteProtocol.protocol decoder).chain H pub pf 26).toProgram).1.map Prod.fst := by
    have hb := hconvert u (hbase u hu)
    have hchain : (LiteralByteProtocol.protocol decoder).chain H pub pf 26 =
        LiteralByteSampler.samp 26 P (pf 26) := by
      change LiteralByteSampler.samp 26 P (pf 26) = _
      rfl
    rw [hchain, hbytesSampler]
    exact hb
  have hi : 26 < (LiteralByteProtocol.protocol decoder).r := by change 26 < 33; decide
  have hvA := FS2.verifier_reads (LiteralByteProtocol.protocol decoder)
    (RawCutTranscriptRun.decisionOnBytes d) H pub pf 26 hi adv.toBytes (htrace adv (Or.inl rfl))
  have hvR := FS2.verifier_reads (LiteralByteProtocol.protocol decoder)
    (RawCutTranscriptRun.decisionOnBytes d) H pub pf 26 hi reseed.toBytes (htrace reseed (Or.inr rfl))
  have hpA : adv.toBytes ∈ (eval H (RawCutProverCompiler.verifier decoder d
      (eval H (experiment prover (verifier decoder d))).2.1.1
      (eval H (experiment prover (verifier decoder d))).2.1.2)).1.map Prod.fst := by
    simpa [RawCutProverCompiler.verifier, hrun, pub, pf] using hvA
  have hpR : reseed.toBytes ∈ (eval H (RawCutProverCompiler.verifier decoder d
      (eval H (experiment prover (verifier decoder d))).2.1.1
      (eval H (experiment prover (verifier decoder d))).2.1.2)).1.map Prod.fst := by
    simpa [RawCutProverCompiler.verifier, hrun, pub, pf] using hvR
  have hreadA := RawCutWordsFromView.verifier_reads_in_experiment decoder d prover H adv.toBytes hpA
  have hreadR := RawCutWordsFromView.verifier_reads_in_experiment decoder d prover H reseed.toBytes hpR
  constructor
  · change adv.toBytes ∈ run.1.map Prod.fst
    simpa [hrun, p, P, pub, pf, H', a, adv] using hreadA
  · change reseed.toBytes ∈ run.1.map Prod.fst
    simpa [hrun, p, P, pub, pf, H', a, adv, reseed] using hreadR

/-- Row 26's trailing-state parser forces its advance before reseed, then its
returned reseed state places row 27 after that parsed input. -/
theorem row26_frame_before_row27
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RawCutProverCompiler.RunView)
    (hrun : run = eval H (experiment prover (verifier decoder d)))
    (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable run.1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable run.1)
    (h26 : LiteralTranscript.valid 26 (run.2.1.2 26))
    (h27 : LiteralTranscript.valid 27 (run.2.1.2 27)) :
    Before run.1 (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 26)
      (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 27) := by
  classical
  let p := SelectedTranscriptParams.params
  let pub := run.2.1.1
  let pf := run.2.1.2
  let P := (LiteralByteProtocol.protocol decoder).transcript H pub pf 26
  obtain ⟨payloadBytes, hbytes⟩ := erased_valid_payload26 (pf 26) (by simpa [pf] using h26)
  let H' : FS2.Duplex.Addr SelectedTranscriptParams.L → State := fun a => H a.toBytes
  let a := UnifiedSampler.absorb p 26 (LiteralTranscript.erasePrefix P) payloadBytes
  let adv := advanceA p (H' a)
  let reseed := OpeningReseedFrame.addr (L := SelectedTranscriptParams.L)
    (LiteralTranscript.erasePrefix P).statement.tag (by norm_num [SelectedTranscriptParams.L]) (H' adv)
  have hframeEq := frame_eq_absorb26 decoder H pub pf payloadBytes hbytes
  have hframe := RWireRawCutLiteralSamplerOrder.ordinary_frame_before_advance decoder d prover H run hrun iv Q
    hQ hout (by decide) (by decide) h26
  have hadvEq : advanceA p (H (RawCutWordsFromView.frame decoder H pub pf 26)) = adv := by
    change advanceA p (H (RawCutWordsFromView.frame decoder H pub pf 26)) = advanceA p (H' a)
    rw [hframeEq]
  have hframe' : Before run.1 (RawCutWordsFromView.frame decoder H pub pf 26) adv.toBytes := by
    change Before run.1 (RawCutWordsFromView.frame decoder H pub pf 26)
      (advanceA p (H (RawCutWordsFromView.frame decoder H pub pf 26))).toBytes at hframe
    rw [hadvEq] at hframe
    exact hframe
  have hreads := reseed_read_pair decoder d prover H run hrun payloadBytes hbytes
  have hframeRes : Read run.1
      ((OpeningReseedFrame.domain ++ [(LiteralTranscript.erasePrefix P).statement.tag]) ++
        bytes (H adv.toBytes)) := by
    simpa only [reseed, OpeningReseedFrame.addr_bytes, H'] using hreads.2
  have hcons : ∀ q ∈ run.1, q.2 = H q.1 := by
    rw [hrun]
    exact FS.eval_consistent H _
  have hresBefore' : Before run.1 adv.toBytes
      ((OpeningReseedFrame.domain ++ [(LiteralTranscript.erasePrefix P).statement.tag]) ++
        bytes (H adv.toBytes)) := by
    exact BinRawByteCollisionTargets.root_before_trailing_frame
      (iv := iv) (H := H) (tr := run.1) (Q := Q) hcons hQ hout
      (pre := OpeningReseedFrame.domain ++ [(LiteralTranscript.erasePrefix P).statement.tag])
      (a := adv.toBytes) hreads.1 hframeRes
  have hresBefore : Before run.1 adv.toBytes reseed.toBytes := by
    simpa only [reseed, OpeningReseedFrame.addr_bytes, H'] using hresBefore' 
  have hstate : UnifiedSampler.stateOf p
      (LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf 27)) = H reseed.toBytes := by
    rw [RawCutLiteralTranscriptSuccessor.actual_successor_state]
    have hchain : (LiteralByteProtocol.protocol decoder).chain H pub pf 26 =
        LiteralByteSampler.samp 26 P (pf 26) := rfl
    rw [hchain]
    have hbytesSampler : LiteralByteSampler.samp 26 P (pf 26) =
        LiteralByteSampler.samp 26 P (.payload payloadBytes) := by
      apply congrArg (ProgramSamplerMap.map Addr.toBytes)
      unfold LiteralTranscript.samp
      rw [hbytes]
      rfl
    rw [hbytesSampler, RawCutLiteralStateSuccessor.reseed_payload_state]
    rfl
  have hnext := RWireRawCutLiteralNextFrame.state_address_before_next_frame decoder d prover H run hrun iv Q hQ hout
    (j := 27) (by decide) (by decide) h27 reseed hstate hreads.2
  have hnext' : Before run.1 reseed.toBytes
      (RawCutWordsFromView.frame decoder H pub pf 27) := by
    simpa only [pub, pf, reseed] using hnext
  exact before_trans run.1 hframe' (before_trans run.1 hresBefore hnext')

#print axioms row26_frame_before_row27

#print axioms erased_valid_payload26
#print axioms firstCell_map
#print axioms frame_eq_absorb26
#print axioms reseed_read_pair
end AspisR1.RWireRawCutLiteralReseedOrder
end
