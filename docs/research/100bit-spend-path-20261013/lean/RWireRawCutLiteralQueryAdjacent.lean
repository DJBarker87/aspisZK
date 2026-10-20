import RWireRawCutLiteralNextFrame
import RawCutLiteralStateSuccessor
import RawCutLiteralTranscriptSuccessor
import RWireRawCutLiteralQueryOrder
import R1QueryContinuation
import R1QuerySamplerBridge
import R1QueryFirstRead
import R1UnifiedSampler
import R1LiteralByteProtocol

set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawCutLiteralQueryAdjacent

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.LiteralTranscript
open AspisR1.UnifiedSampler
open AspisR1.QuerySamplerBridge
open AspisR1.RawCutWordsFromView
open AspisR1.RawCutProverCompiler
open AspisR1.BinRawByteCollisionTargets

private theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (label : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map label s) = (firstCell s).map label := by
  cases s <;> rfl

private theorem erased_valid_payload31 (m : LiteralTranscript.Message)
    (hm : LiteralTranscript.valid 31 m) :
    ∃ bytes, LiteralTranscript.erase m = .payload bytes := by
  cases m with
  | initial root word => simp [LiteralTranscript.valid] at hm
  | payload bytes => exact ⟨bytes, rfl⟩
  | c2 bytes word => exact ⟨bytes, rfl⟩
  | second bytes word => exact ⟨bytes, rfl⟩

private theorem query_frame_eq_absorb
    (decoder : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (payloadBytes : SelectedTranscriptParams.Message)
    (hm : LiteralTranscript.erase (pf 31) = .payload payloadBytes) :
    RawCutWordsFromView.frame decoder H pub pf 31 =
      (UnifiedSampler.absorb SelectedTranscriptParams.params 31
        (LiteralTranscript.erasePrefix
          ((LiteralByteProtocol.protocol decoder).transcript H pub pf 31))
        payloadBytes).toBytes := by
  unfold RawCutWordsFromView.frame
  change (firstCell (ProgramSamplerMap.map Addr.toBytes
      (LiteralTranscript.samp 31
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf 31)
        (pf 31)))).getD [] = _
  have hsampler : LiteralTranscript.samp 31
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 31) (pf 31) =
      LiteralTranscript.samp 31
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf 31)
        (.payload payloadBytes) := by
    unfold LiteralTranscript.samp
    rw [hm]
    simp [LiteralTranscript.erase]
  have hD : 5 ≤ SelectedTranscriptParams.params.D := by
    norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D]
  have hfirst : firstCell (LiteralTranscript.samp 31
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 31)
      (.payload payloadBytes)) = some
      (UnifiedSampler.absorb SelectedTranscriptParams.params 31
        (LiteralTranscript.erasePrefix
          ((LiteralByteProtocol.protocol decoder).transcript H pub pf 31))
        payloadBytes) := by
    change firstCell (UnifiedSampler.samp SelectedTranscriptParams.params hD 31
      (LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf 31))
      (.payload payloadBytes)) = _
    rw [UnifiedSampler.row_query SelectedTranscriptParams.params hD
    (LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 31)) payloadBytes]
    simp [QuerySamplerBridge.sampler, FS2.firstCell]
  rw [firstCell_map]
  rw [hsampler]
  rw [hfirst]
  rfl

private theorem query_read_pair
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RunView)
    (hrun : run = eval H (experiment prover (verifier decoder d)))
    (payloadBytes : SelectedTranscriptParams.Message)
    (hbytes : LiteralTranscript.erase (run.2.1.2 31) = .payload payloadBytes)
    (k : Nat) (hk : k < 8) :
    Read run.1 (squeezeA SelectedTranscriptParams.params
      (QuerySampler.state SelectedTranscriptParams.params
        (fun a : FS2.Duplex.Addr SelectedTranscriptParams.L => H a.toBytes)
        (H ((UnifiedSampler.absorb SelectedTranscriptParams.params 31
          (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol decoder).transcript H
            run.2.1.1 run.2.1.2 31)) payloadBytes).toBytes)) k)).toBytes ∧
    Read run.1 (advanceA SelectedTranscriptParams.params
      (QuerySampler.state SelectedTranscriptParams.params
        (fun a : FS2.Duplex.Addr SelectedTranscriptParams.L => H a.toBytes)
        (H ((UnifiedSampler.absorb SelectedTranscriptParams.params 31
          (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol decoder).transcript H
            run.2.1.1 run.2.1.2 31)) payloadBytes).toBytes)) k)).toBytes := by
  classical
  let p := SelectedTranscriptParams.params
  let pub := run.2.1.1
  let pf := run.2.1.2
  let P := (LiteralByteProtocol.protocol decoder).transcript H pub pf 31
  let H' : FS2.Duplex.Addr SelectedTranscriptParams.L → State := fun a => H a.toBytes
  let c := UnifiedSampler.absorb p 31 (LiteralTranscript.erasePrefix P) payloadBytes
  let s := QuerySampler.state p H' (H' c)
  have hD : 5 ≤ p.D := by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]
  have htyped : LiteralTranscript.samp 31 P (pf 31) = LiteralTranscript.samp 31 P (.payload payloadBytes) := by
    unfold LiteralTranscript.samp
    rw [hbytes]
    rfl
  have hbytesSampler : LiteralByteSampler.samp 31 P (pf 31) = LiteralByteSampler.samp 31 P (.payload payloadBytes) :=
    congrArg (ProgramSamplerMap.map Addr.toBytes) htyped
  have hquery : LiteralTranscript.samp 31 P (.payload payloadBytes) =
      QuerySamplerBridge.sampler p c UnifiedSampler.liftQuery := by
    change UnifiedSampler.samp p hD 31 (LiteralTranscript.erasePrefix P)
      (.payload payloadBytes) = _
    rw [UnifiedSampler.row_query p hD (LiteralTranscript.erasePrefix P) payloadBytes]
  have hmap := congrArg (fun z => z.1.map Prod.fst)
    (LiteralByteSampler.eval_eq H 31 P (.payload payloadBytes))
  have hconvert (u : Addr SelectedTranscriptParams.L)
      (hu : u ∈ (eval H' (LiteralTranscript.samp 31 P (.payload payloadBytes)).toProgram).1.map Prod.fst) :
      u.toBytes ∈ (eval H (LiteralByteSampler.samp 31 P (.payload payloadBytes)).toProgram).1.map Prod.fst := by
    rw [LiteralByteSampler.eval_eq]
    simp only [AspisV8R19.OracleProgramOps.mapView, List.map_map, Function.comp_def]
    rcases List.mem_map.mp hu with ⟨q, hpair, haddr⟩
    rcases q with ⟨addr, state⟩
    apply List.mem_map.mpr
    refine ⟨(addr, state), hpair, ?_⟩
    exact congrArg Addr.toBytes haddr
  have htypedReads := QuerySamplerBridge.reads_pairs (p := p) (H := H')
    (C := LiteralTranscript.Challenge) c UnifiedSampler.liftQuery k hk
  have hsqBytes := hconvert _ (by simpa [hquery, QuerySamplerBridge.sampler, s, H'] using htypedReads.1)
  have hadvBytes := hconvert _ (by simpa [hquery, QuerySamplerBridge.sampler, s, H'] using htypedReads.2)
  have hchain : (LiteralByteProtocol.protocol decoder).chain H pub pf 31 =
      LiteralByteSampler.samp 31 P (pf 31) := by
    change LiteralByteSampler.samp 31 P (pf 31) = _
    rfl
  have hsqTrace : (squeezeA p (s k)).toBytes ∈
      (eval H ((LiteralByteProtocol.protocol decoder).chain H pub pf 31).toProgram).1.map Prod.fst := by
    rw [hchain, hbytesSampler]
    exact hsqBytes
  have hadvTrace : (advanceA p (s k)).toBytes ∈
      (eval H ((LiteralByteProtocol.protocol decoder).chain H pub pf 31).toProgram).1.map Prod.fst := by
    rw [hchain, hbytesSampler]
    exact hadvBytes
  have hi : 31 < (LiteralByteProtocol.protocol decoder).r := by change 31 < 33; decide
  have hsqV := FS2.verifier_reads (LiteralByteProtocol.protocol decoder)
    (RawCutTranscriptRun.decisionOnBytes d) H pub pf 31 hi _ hsqTrace
  have hadvV := FS2.verifier_reads (LiteralByteProtocol.protocol decoder)
    (RawCutTranscriptRun.decisionOnBytes d) H pub pf 31 hi _ hadvTrace
  have hsqExp : (squeezeA p (s k)).toBytes ∈
      (eval H (RawCutProverCompiler.verifier decoder d
        (eval H (experiment prover (verifier decoder d))).2.1.1
        (eval H (experiment prover (verifier decoder d))).2.1.2)).1.map Prod.fst := by
    simpa [RawCutProverCompiler.verifier, hrun, pub, pf] using hsqV
  have hadvExp : (advanceA p (s k)).toBytes ∈
      (eval H (RawCutProverCompiler.verifier decoder d
        (eval H (experiment prover (verifier decoder d))).2.1.1
        (eval H (experiment prover (verifier decoder d))).2.1.2)).1.map Prod.fst := by
    simpa [RawCutProverCompiler.verifier, hrun, pub, pf] using hadvV
  have hsqRead := RawCutWordsFromView.verifier_reads_in_experiment
    decoder d prover H (squeezeA p (s k)).toBytes hsqExp
  have hadvRead := RawCutWordsFromView.verifier_reads_in_experiment
    decoder d prover H (advanceA p (s k)).toBytes hadvExp
  constructor
  · change (squeezeA p (s k)).toBytes ∈ run.1.map Prod.fst
    simpa [hrun] using hsqRead
  · change (advanceA p (s k)).toBytes ∈ run.1.map Prod.fst
    simpa [hrun] using hadvRead

/-- The selected advance returned by row 31 occurs after its commitment
frame and before the next row's frame, under the raw-byte no-collision event. -/
theorem row31_frame_before_row32
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RunView)
    (hrun : run = eval H (experiment prover (verifier decoder d)))
    (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable run.1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable run.1)
    (h31 : LiteralTranscript.valid 31 (run.2.1.2 31))
    (h32 : LiteralTranscript.valid 32 (run.2.1.2 32)) :
    Before run.1 (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 31)
      (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 32) := by
  classical
  let p := SelectedTranscriptParams.params
  let pub := run.2.1.1
  let pf := run.2.1.2
  let P := (LiteralByteProtocol.protocol decoder).transcript H pub pf 31
  obtain ⟨payloadBytes, hbytes⟩ := erased_valid_payload31 (pf 31) (by simpa [pf] using h31)
  let H' : FS2.Duplex.Addr SelectedTranscriptParams.L → State := fun a => H a.toBytes
  let c := UnifiedSampler.absorb p 31 (LiteralTranscript.erasePrefix P) payloadBytes
  let cBytes := c.toBytes
  let s := QuerySampler.state p H' (H' c)
  let qresult := QueryFirstRead.result p H' s
  have hframe := query_frame_eq_absorb decoder H pub pf payloadBytes hbytes
  have hroot : s 0 = H cBytes := by
    change H cBytes = H cBytes
    rfl
  have hsteps : ∀ j < 7, s (j + 1) = H ((advanceA p (s j)).toBytes) := by
    intro j hj
    simp [s, QuerySamplerBridge.state_step, H']
  have hreads : ∀ k < 8,
      Read run.1 (squeezeA p (s k)).toBytes ∧ Read run.1 (advanceA p (s k)).toBytes := by
    intro k hk
    exact query_read_pair decoder d prover H run hrun payloadBytes hbytes k hk
  have hselected : qresult.2 ∈ (List.range 8).map (fun k => s (k + 1)) := by
    exact QueryContinuation.eight_pair_continuation
      (QueryStateList.blocks p H' s 8) (QueryStateList.advances s 8) (s 0)
      (by simp [QueryStateList.blocks]) (by simp [QueryStateList.advances])
  obtain ⟨k, hk, hsel⟩ := List.mem_map.mp hselected
  have hk8 : k < 8 := List.mem_range.mp hk
  have hstate : UnifiedSampler.stateOf p
      (LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf 32)) = H ((advanceA p (s k)).toBytes) := by
    have hsucc := RawCutLiteralTranscriptSuccessor.actual_successor_state decoder H pub pf 31
    have hrow := RawCutLiteralStateSuccessor.query_payload_state H P payloadBytes
    have hchain : (LiteralByteProtocol.protocol decoder).chain H pub pf 31 =
        LiteralByteSampler.samp 31 P (pf 31) := by
      change LiteralByteSampler.samp 31 P (pf 31) = _
      rfl
    have hbytesSampler : LiteralByteSampler.samp 31 P (pf 31) =
        LiteralByteSampler.samp 31 P (.payload payloadBytes) := by
      apply congrArg (ProgramSamplerMap.map Addr.toBytes)
      unfold LiteralTranscript.samp
      rw [hbytes]
      rfl
    rw [hchain, hbytesSampler] at hsucc
    rw [hrow] at hsucc
    change UnifiedSampler.stateOf p
      (LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf 32)) =
      (QueryFirstRead.result p H' s).2 at hsucc
    rw [← hsel] at hsucc
    simpa [s, QuerySampler.state, H'] using hsucc
  have hpairRead := query_read_pair decoder d prover H run hrun payloadBytes hbytes k hk8
  have hreadA := hpairRead.2
  have hrootBefore := RWireRawCutLiteralQueryOrder.root_before_chain p H run.1 Q iv
      (by rw [hrun]; exact FS.eval_consistent H _)
      hQ hout cBytes
      (by
        have hfr := RawCutWordsFromView.frame_read decoder d prover H 31 (by decide)
        have hfr' : Read run.1 (RawCutWordsFromView.frame decoder H pub pf 31) := by
          simpa [hrun, pub, pf] using hfr
        simpa [cBytes, c, p, P, hframe] using hfr')
      s hroot hsteps hreads
  have hprev : Before run.1
      (RawCutWordsFromView.frame decoder H pub pf 31) ((advanceA p (s k)).toBytes) := by
    rw [hframe]
    exact (hrootBefore k hk8).2
  have hnext := RWireRawCutLiteralNextFrame.state_address_before_next_frame decoder d prover H run hrun
    iv Q hQ hout (j := 32) (by decide) (by decide) h32
    (advanceA p (s k)) hstate hreadA
  exact before_trans run.1 hprev hnext

#print axioms firstCell_map
#print axioms erased_valid_payload31
#print axioms query_frame_eq_absorb
#print axioms query_read_pair
#print axioms row31_frame_before_row32
end AspisR1.RWireRawCutLiteralQueryAdjacent

#print axioms AspisR1.RWireRawCutLiteralQueryAdjacent.row31_frame_before_row32
end
