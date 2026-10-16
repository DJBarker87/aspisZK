import RawAdaptiveDecoderInjection
import AcceptedAdaptiveMembershipSoundness

/-! The concrete public-free decoder discharges the recovery premise in the
adaptive membership reduction. The remaining source-facing obligations are
acceptance-to-formatting, terminal rejection outside the shared collision
event, and the total distinct-query budget. This is a symbolic query-dependent
ROM bound, separate from the fresh per-attempt 100-bit arithmetic theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawAdaptiveMembershipBound
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound

private theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (f : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map f s) = (firstCell s).map f := by
  cases s <;> rfl

theorem chains_read (decoder : LiteralByteProtocol.Decoder) :
    ChainsRead (LiteralByteProtocol.protocol decoder) := by
  intro i P m hi
  change firstCell (ProgramSamplerMap.map Addr.toBytes (LiteralTranscript.samp i P m)) ≠ none
  rw [firstCell_map]
  have hn : firstCell (LiteralTranscript.samp i P m) ≠ none :=
    UnifiedSampler.firstCell_some _ _ _ _ _
  cases h : firstCell (LiteralTranscript.samp i P m) with
  | none => exact absurd h hn
  | some a => simp

private theorem firstCell_mem {I A C : Type} [DecidableEq I] [Inhabited A]
    (H : I → A) (s : Sampler I A C) (a : I) (ha : firstCell s = some a) :
    a ∈ (eval H s.toProgram).1.map Prod.fst := by
  cases s with
  | done c => cases ha
  | ask i k =>
      simp only [firstCell,Option.some.injEq] at ha
      subst i
      exact List.mem_cons_self ..
  | multi c cs nd k =>
      simp only [firstCell,Option.some.injEq] at ha
      subst c
      exact List.mem_cons_self ..

theorem verifier_reads (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool) :
    ReadsChains (LiteralByteProtocol.protocol decoder) (RawCutProverCompiler.verifier decoder d) := by
  intro H pub pf i a hi ha
  apply FS2.verifier_reads (LiteralByteProtocol.protocol decoder)
    (RawCutTranscriptRun.decisionOnBytes d) H pub pf i hi a
  exact firstCell_mem H _ a ha

theorem membership_bound
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : RawCutProverCompiler.Prover) (Q : Nat)
    (hQ : ∀ H : Bytes → State, firstReads emptyTable
      (eval H (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d))).1 ≤ Q)
    (hformat : ∀ H : Bytes → State,
      FS2.accepts (eval H (RawCutProverCompiler.experiment prover
        (RawCutProverCompiler.verifier decoder d))) →
      let run := eval H (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d))
      (∀ i < 33, LiteralTranscript.valid i (run.2.1.2 i)) ∧
        run.2.1.1.tag = 2 ∧ RawAdaptiveDecoderInjection.CommitmentMessages run.2.1.2)
    (hterminal : AcceptedAdaptiveFiatShamir.D3Outside (LiteralByteProtocol.protocol decoder)
      LiteralByteProtocol.rows
      (RawCutProverCompiler.compiled decoder d (RawCutWordsFromView.buildWords decoder) prover)
      (RawCutProverCompiler.verifier decoder d) (RawAdaptiveDecoderInjection.collision Q)) :
    lazyMean (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d)) emptyTable
      (fun v => indicator (FS2.accepts v ∧ ¬ ∃ w, LiteralProtocol.relation v.2.1.1 w)) ≤
      (Q : ℚ) * maxErr LiteralByteProtocol.rows.ε 33 + RawAdaptiveDecoderInjection.kappa Q := by
  let cp := RawCutProverCompiler.compiled decoder d (RawCutWordsFromView.buildWords decoder) prover
  let dec := RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select LiteralTableWordChoice.choose
  let inj := RawAdaptiveDecoderInjection.injection decoder d prover Q hQ hformat
  have hqc := RawCutCompilerLaw.query_bound_preserved decoder d
    (RawCutWordsFromView.buildWords decoder) prover Q hQ
  have hb := AcceptedAdaptiveMembershipSoundness.membership_bound_outside
    (LiteralByteProtocol.protocol decoder) LiteralByteProtocol.rows dec LiteralProtocol.relation
    (fun _ _ => rfl) cp (RawCutProverCompiler.verifier decoder d)
    RawAdaptiveDecoderInjection.kappa Q (LiteralByteProtocol.d1 decoder)
    (RawAdaptiveLiteralDecoder.density decoder RawFullPublicSelection.select LiteralTableWordChoice.choose)
    (chains_read decoder) (verifier_reads decoder d) inj hterminal hqc
  exact RawCutCompilerLaw.transfer_membership_bound LiteralProtocol.relation decoder d
    (RawCutWordsFromView.buildWords decoder) prover _ hb

#print axioms chains_read
#print axioms verifier_reads
#print axioms membership_bound
end AspisR1.RawAdaptiveMembershipBound
end
