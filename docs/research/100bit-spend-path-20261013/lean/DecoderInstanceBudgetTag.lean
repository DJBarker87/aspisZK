import RawDeployedTranscriptFormat
import QvStage1Count
import R1VerifierCallBudget

/-! R18 and R19 interfaces for a future frozen-source instance. Neither public
mapping nor complete source-log coverage follows from a free D/d. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.DecoderInstanceBudgetTag
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open RawCutTranscriptRun RawCutProverCompiler

/-- htag has no acceptance restriction. This is the required public-map
obligation for the original experiment, including rejected runs. -/
theorem htag_of_public_map (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (bytes : List SemanticPublicWire.Byte) (pub : R0P.Public SemanticPublicWire.M31)
    (hparse : SemanticPublicWire.parsePublic bytes = some pub)
    (AcceptedSourcePublicMap : ∀ H : Bytes → State,
      (eval H (experiment P (verifier D d))).2.1.1 =
        SelectedTranscriptParams.publicStatement bytes pub hparse) :
    ∀ H : Bytes → State, (eval H (experiment P (verifier D d))).2.1.1.tag = 2 := by
  exact RawDeployedTranscriptFormat.mapped_public_tag
    (fun H => eval H (experiment P (verifier D d))) bytes pub hparse AcceptedSourcePublicMap

/-- The exact hQ shape; QP remains adversary-side and Q2 is the universal
stage-2 constant still to be proved. Repeats are conservatively charged. -/
def hQShape (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (QP Q2 : Nat) : Prop :=
  ∀ H : Bytes → State,
    firstReads emptyTable (eval H (experiment P (verifier D d))).1 ≤ QP + 595 + Q2

/-- Whole-experiment coverage, including failure/suspension: the log is
covered by prover, tx1, and tx2 calls. Perm is used ONLY for accounting;
this definition does not assert execution order or oracle correspondence. -/
def CompleteLogCoverage (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (QP Q2 : Nat) : Prop :=
  ∀ H : Bytes → State, ∃ prover tx1 tx2 : List (Bytes × State),
    (eval H (experiment P (verifier D d))).1.Perm (prover ++ tx1 ++ tx2) ∧
    prover.length ≤ QP ∧ QvStage1.CountedTrace 10 tx1 ∧ tx2.length ≤ Q2

/-- Named coverage is still owed by R10/R19/R20. The existing R19 count
supplies the 595 term without importing the retired 328-call route. -/
theorem hQ_of_complete_log_coverage (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (QP Q2 : Nat)
    (coverage : CompleteLogCoverage D d P QP Q2) : hQShape D d P QP Q2 := by
  intro H
  obtain ⟨prover, tx1, tx2, hp, hprover, htx1, htx2⟩ := coverage H
  have hone := QvStage1.countedTrace_bound htx1
  rw [QvStage1.stage1Budget_ten] at hone
  have hlen := hp.length_eq
  simp only [List.length_append] at hlen
  have hreads := VerifierCallBudget.firstReads_le_length emptyTable
    (eval H (experiment P (verifier D d))).1
  omega

#print axioms htag_of_public_map
#print axioms hQ_of_complete_log_coverage
end AspisR1.DecoderInstanceBudgetTag
end
