import RawCutLiteralInitialAdvanceRead
import RWireRawCutLiteralNextFrame
import RawCutWordsFromView
import RawCutProverCompiler
import BinRawByteCollisionTargets
import R1PublicInitFrame
import R1LiteralByteProtocol
import R1LiteralByteSampler
import R1UnifiedSampler
import R1DuplexSamplers

set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawCutLiteralRowZeroOrder

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

private theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (label : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map label s) = (firstCell s).map label := by
  cases s <;> rfl

/-- The public initialization frame, its dedicated row-zero absorb, and the
actual row-zero advance occur in that order in the raw experiment trace. -/
theorem row_zero_frame_before_advance
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RawCutProverCompiler.RunView)
    (hrun : run = eval H (experiment prover (verifier decoder d)))
    (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable run.1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable run.1)
    (hvalid : LiteralTranscript.valid 0 (run.2.1.2 0)) :
    let c1 := match run.2.1.2 0 with | .initial c1 _ => c1 | _ => default
    let init := PublicInitFrame.addr run.2.1.1.pubBytes run.2.1.1.initFits c1
    let row0 := PublicInitFrame.row0 SelectedTranscriptParams.params
      (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
      (H init.toBytes)
    Before run.1
      (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 0)
      (advanceA SelectedTranscriptParams.params (H row0.toBytes)).toBytes := by
  classical
  cases hmsg : run.2.1.2 0 with
  | initial c1 word =>
      let p := SelectedTranscriptParams.params
      let pub := run.2.1.1
      let pf := run.2.1.2
      let P := (LiteralByteProtocol.protocol decoder).transcript H pub pf 0
      have hD : 5 ≤ p.D := by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]
      let init := PublicInitFrame.addr pub.pubBytes pub.initFits c1
      let row0 := PublicInitFrame.row0 p hD (H init.toBytes)
      let adv := advanceA p (H row0.toBytes)
      have hrow : LiteralTranscript.samp 0 P (.initial c1 word) =
          DuplexSamplers.initial p init (PublicInitFrame.row0 p hD) 0
            AspisR1.TranscriptView.liftChallenge := by
        change UnifiedSampler.samp p hD 0 (LiteralTranscript.erasePrefix P) (.initial c1) = _
        exact UnifiedSampler.row_zero p hD (LiteralTranscript.erasePrefix P) c1
      have hframe : RawCutWordsFromView.frame decoder H pub pf 0 = init.toBytes := by
        unfold RawCutWordsFromView.frame
        change (firstCell (ProgramSamplerMap.map Addr.toBytes
          (LiteralTranscript.samp 0 P (pf 0)))).getD [] = _
        have hpf : pf 0 = .initial c1 word := by simpa [pf] using hmsg
        rw [hpf, firstCell_map, hrow]
        simp [DuplexSamplers.initial, FS2.firstCell, init]
      have hreadInit : Read run.1 init.toBytes := by
        have h := RawCutWordsFromView.frame_read decoder d prover H 0 (by decide)
        have h' : Read run.1 (RawCutWordsFromView.frame decoder H pub pf 0) := by
          simpa [hrun, pub, pf] using h
        simpa [hframe] using h'
      let H' : FS2.Duplex.Addr SelectedTranscriptParams.L → State := fun a => H a.toBytes
      have hrow0Mem : row0 ∈
          (eval H' (LiteralTranscript.samp 0 P (.initial c1 word)).toProgram).1.map Prod.fst := by
        rw [hrow]
        simp [DuplexSamplers.initial_eval, init, row0, H']
      have hrow0Bytes : row0.toBytes ∈
          (eval H (LiteralByteSampler.samp 0 P (.initial c1 word)).toProgram).1.map Prod.fst := by
        rw [LiteralByteSampler.eval_eq]
        simp only [AspisV8R19.OracleProgramOps.mapView, List.map_map, Function.comp_def]
        rcases List.mem_map.mp hrow0Mem with ⟨q, hq, haddr⟩
        rcases q with ⟨a, state⟩
        apply List.mem_map.mpr
        refine ⟨(a, state), hq, ?_⟩
        exact congrArg Addr.toBytes haddr
      have hbytesSampler : LiteralByteSampler.samp 0 P (pf 0) =
          LiteralByteSampler.samp 0 P (.initial c1 word) := by
        apply congrArg (ProgramSamplerMap.map Addr.toBytes)
        unfold LiteralTranscript.samp
        have hpf : pf 0 = .initial c1 word := by simpa [pf] using hmsg
        rw [hpf]
      have hchain : (LiteralByteProtocol.protocol decoder).chain H pub pf 0 =
          LiteralByteSampler.samp 0 P (pf 0) := by
        change LiteralByteSampler.samp 0 P (pf 0) = _
        rfl
      have htrace : row0.toBytes ∈
          (eval H ((LiteralByteProtocol.protocol decoder).chain H pub pf 0).toProgram).1.map Prod.fst := by
        rw [hchain, hbytesSampler]
        exact hrow0Bytes
      have hi : 0 < (LiteralByteProtocol.protocol decoder).r := by change 0 < 33; decide
      have hverifier := FS2.verifier_reads (LiteralByteProtocol.protocol decoder)
        (RawCutTranscriptRun.decisionOnBytes d) H pub pf 0 hi row0.toBytes htrace
      have htraceExp : row0.toBytes ∈
          (eval H (RawCutProverCompiler.verifier decoder d
            (eval H (experiment prover (verifier decoder d))).2.1.1
            (eval H (experiment prover (verifier decoder d))).2.1.2)).1.map Prod.fst := by
        simpa [RawCutProverCompiler.verifier, hrun, pub, pf] using hverifier
      have hreadRow0 := RawCutWordsFromView.verifier_reads_in_experiment
        decoder d prover H row0.toBytes htraceExp
      have hreadRow0' : Read run.1 row0.toBytes := by
        change row0.toBytes ∈ run.1.map Prod.fst
        simpa [hrun] using hreadRow0
      have hfirst : Before run.1 init.toBytes row0.toBytes := by
        apply BinRawByteCollisionTargets.duplex_state_before_frame iv H run.1 Q
          (by rw [hrun]; exact FS.eval_consistent H _) hQ hout init.toBytes row0.toBytes
          hreadInit hreadRow0'
        rw [PublicInitFrame.row0_prefix]
      have hadvance : Read run.1 adv.toBytes := by
        obtain ⟨c1', word', hp, ha⟩ := RawCutLiteralInitialAdvanceRead.initial_advance_read
          decoder d prover H run hrun (by simpa [pf] using hvalid)
        have hp' : c1' = c1 ∧ word' = word := by
          rw [hmsg] at hp
          cases hp
          exact ⟨rfl, rfl⟩
        rcases hp' with ⟨rfl, rfl⟩
        simpa [p, pub, pf, row0, adv, init] using ha
      have hsecond : Before run.1 row0.toBytes adv.toBytes := by
        apply BinRawByteCollisionTargets.duplex_state_before_frame iv H run.1 Q
          (by rw [hrun]; exact FS.eval_consistent H _) hQ hout row0.toBytes adv.toBytes
          hreadRow0' hadvance
        exact FS2.Duplex.toBytes_advanceA p (H row0.toBytes)
      have hordered := before_trans run.1 hfirst hsecond
      simpa [hframe, p, pub, pf, row0, adv, init] using hordered
  | payload bytes => rw [hmsg] at hvalid; simp [LiteralTranscript.valid] at hvalid
  | c2 bytes word => rw [hmsg] at hvalid; simp [LiteralTranscript.valid] at hvalid
  | second bytes word => rw [hmsg] at hvalid; simp [LiteralTranscript.valid] at hvalid

#print axioms row_zero_frame_before_advance

#print axioms firstCell_map
end AspisR1.RWireRawCutLiteralRowZeroOrder
end
