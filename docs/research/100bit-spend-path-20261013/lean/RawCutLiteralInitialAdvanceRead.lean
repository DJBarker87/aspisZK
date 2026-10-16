import RawCutLiteralStateSuccessor
import RawCutLiteralTranscriptSuccessor
import R1PublicInitFrame
import RawCutWordsFromView
import RawCutProverCompiler
import RawByteCollisionTargets

set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCutLiteralInitialAdvanceRead

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.LiteralTranscript
open AspisR1.UnifiedSampler
open AspisR1.DuplexSamplers
open AspisR1.RawCutWordsFromView
open AspisR1.RawCutProverCompiler
open AspisR1.RawByteCollisionTargets

theorem initial_advance_read
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RunView)
    (hrun : run = eval H (experiment prover (verifier decoder d)))
    (hm : LiteralTranscript.valid 0 (run.2.1.2 0)) :
    ∃ c1 word,
      run.2.1.2 0 = .initial c1 word ∧
      Read run.1
        ((advanceA SelectedTranscriptParams.params
          (H (PublicInitFrame.row0 SelectedTranscriptParams.params
            (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
            (H (PublicInitFrame.addr run.2.1.1.pubBytes
              run.2.1.1.initFits c1).toBytes)).toBytes)).toBytes) := by
  cases hmsg : run.2.1.2 0 with
  | initial c1 word =>
      refine ⟨c1, word, rfl, ?_⟩
      let p := SelectedTranscriptParams.params
      let pub := run.2.1.1
      let pf := run.2.1.2
      let P := (LiteralByteProtocol.protocol decoder).transcript H pub pf 0
      have hD : 5 ≤ p.D := by
        norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]
      let init := PublicInitFrame.addr pub.pubBytes pub.initFits c1
      let a := PublicInitFrame.row0 p hD (H init.toBytes)
      let adv := advanceA p (H a.toBytes)
      have hrow : LiteralTranscript.samp 0 P (.initial c1 word) =
          DuplexSamplers.initial p init (PublicInitFrame.row0 p hD) 0
            AspisR1.TranscriptView.liftChallenge := by
        change UnifiedSampler.samp p hD 0 (LiteralTranscript.erasePrefix P)
          (.initial c1) = _
        exact UnifiedSampler.row_zero p hD (LiteralTranscript.erasePrefix P) c1
      have hmem : adv ∈
          (eval (fun x : FS2.Duplex.Addr SelectedTranscriptParams.L => H x.toBytes)
            (LiteralTranscript.samp 0 P (.initial c1 word)).toProgram).1.map Prod.fst := by
        rw [hrow, DuplexSamplers.initial_eval]
        simp [adv, a, init]
      have hmap := congrArg (fun z => z.1.map Prod.fst)
        (LiteralByteSampler.eval_eq H 0 P (.initial c1 word))
      have hmemBytes : adv.toBytes ∈
          (eval H (LiteralByteSampler.samp 0 P (.initial c1 word)).toProgram).1.map Prod.fst := by
        rw [hmap]
        simp only [AspisV8R19.OracleProgramOps.mapView, List.map_map, Function.comp_def]
        rcases List.mem_map.mp hmem with ⟨q, hq, haddr⟩
        rcases q with ⟨addr, state⟩
        have haddr' : addr = adv := haddr
        subst addr
        exact List.mem_map.mpr ⟨(adv, state), hq, rfl⟩
      have hchain : (LiteralByteProtocol.protocol decoder).chain H pub pf 0 =
          LiteralByteSampler.samp 0 P (.initial c1 word) := by
        change LiteralByteSampler.samp 0 P (pf 0) =
          LiteralByteSampler.samp 0 P (.initial c1 word)
        have hpf : pf 0 = .initial c1 word := by simpa [pf] using hmsg
        rw [hpf]
      have hchainTrace : adv.toBytes ∈
          (eval H ((LiteralByteProtocol.protocol decoder).chain H pub pf 0).toProgram).1.map Prod.fst := by
        rw [hchain]
        exact hmemBytes
      have hi : 0 < (LiteralByteProtocol.protocol decoder).r := by
        change 0 < 33
        decide
      have hverifier := FS2.verifier_reads (LiteralByteProtocol.protocol decoder)
        (RawCutTranscriptRun.decisionOnBytes d) H pub pf 0 hi adv.toBytes hchainTrace
      have htraceExp : adv.toBytes ∈
          (eval H (RawCutProverCompiler.verifier decoder d
            (eval H (experiment prover (verifier decoder d))).2.1.1
            (eval H (experiment prover (verifier decoder d))).2.1.2)).1.map Prod.fst := by
        simpa [RawCutProverCompiler.verifier, hrun, pub, pf] using hverifier
      have hrunRead := RawCutWordsFromView.verifier_reads_in_experiment
        decoder d prover H adv.toBytes htraceExp
      change adv.toBytes ∈ run.1.map Prod.fst
      simpa [hrun, p, a, adv, init] using hrunRead
  | payload bytes => rw [hmsg] at hm; simp [LiteralTranscript.valid] at hm
  | c2 bytes word => rw [hmsg] at hm; simp [LiteralTranscript.valid] at hm
  | second bytes word => rw [hmsg] at hm; simp [LiteralTranscript.valid] at hm

#print axioms initial_advance_read
end AspisR1.RawCutLiteralInitialAdvanceRead
end
