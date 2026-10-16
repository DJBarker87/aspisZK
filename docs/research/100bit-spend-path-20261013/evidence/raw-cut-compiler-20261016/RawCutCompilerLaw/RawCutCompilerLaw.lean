import RawCutProverCompiler
import OracleProgramLawExt

/-! The recording/annotation transformation preserves adaptive membership
failure probability under the actual lazy oracle law, and preserves its
distinct-query budget. This is a lossless compiler reduction; it does not
assert that its still-open literal-protocol soundness premises are proved. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCutCompilerLaw

open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.CausalFirstHitUnionBound
open CanonicalCutEnrichedTranscript RawCutTranscriptRun RawCutProverCompiler

theorem membership_probability_eq {W : Type}
    (relation : RawCutProverCompiler.Public → W → Prop)
    (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (buildWords : RunView → Words) (P : Prover) :
    lazyMean (experiment P (verifier decoder d)) emptyTable
        (fun v => indicator (FS2.accepts v ∧ ¬ ∃ w, relation v.2.1.1 w)) =
      lazyMean (experiment (compiled decoder d buildWords P) (verifier decoder d)) emptyTable
        (fun v => indicator (FS2.accepts v ∧ ¬ ∃ w, relation v.2.1.1 w)) := by
  apply OracleProgramLawExt.lazyMean_eq_of_eval
  intro H
  obtain ⟨hpub, hacc⟩ := public_and_acceptance decoder d buildWords P H
  unfold FS2.accepts
  rw [hpub, hacc]

theorem query_bound_preserved (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (buildWords : RunView → Words) (P : Prover) (Q : Nat)
    (hQ : ∀ H : Bytes → State,
      firstReads emptyTable (eval H (experiment P (verifier decoder d))).1 ≤ Q) :
    ∀ H : Bytes → State, firstReads emptyTable
      (eval H (experiment (compiled decoder d buildWords P) (verifier decoder d))).1 ≤ Q := by
  intro H
  rw [RawCutProverCompiler.firstReads_eq]
  exact hQ H

/-- Any proved bound for the constructed literal-word adversary transfers
to the original byte-message adversary without a probability loss. -/
theorem transfer_membership_bound {W : Type}
    (relation : RawCutProverCompiler.Public → W → Prop)
    (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (buildWords : RunView → Words) (P : Prover) (bound : ℚ)
    (hbound : lazyMean
      (experiment (compiled decoder d buildWords P) (verifier decoder d)) emptyTable
      (fun v => indicator (FS2.accepts v ∧ ¬ ∃ w, relation v.2.1.1 w)) ≤ bound) :
    lazyMean (experiment P (verifier decoder d)) emptyTable
      (fun v => indicator (FS2.accepts v ∧ ¬ ∃ w, relation v.2.1.1 w)) ≤ bound := by
  rw [membership_probability_eq relation decoder d buildWords P]
  exact hbound

#print axioms membership_probability_eq
#print axioms query_bound_preserved
#print axioms transfer_membership_bound
end AspisR1.RawCutCompilerLaw
end
