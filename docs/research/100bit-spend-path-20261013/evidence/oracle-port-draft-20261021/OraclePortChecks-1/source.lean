import OraclePortAdmission
import OraclePortConsumer
import D0TypedChecks

/-! HCHECKS composition on the generalized compiled rows. The typedAccepted
argument is the precise remaining byte/opening-to-reader binding frontier;
it is not an established property of the admitted multiproof kernel. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortChecks
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open RawCutProverCompiler (Prover)
open OraclePortExperiment (Decision original recorded)
open OraclePortAdmission
open LiteralAcceptanceTerminal
open RecordedBinaryExperimentBin (SourceInputs)

theorem hchecks (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover)
    (H : Bytes → State) (i : SourceInputs)
    (instanceFields : InstanceFields D dO P H i)
    (typedAccepted : D0TypedChecks.verify (compiledRows D dO P H) i = true) :
    Nonempty (Checks (compiledPublic D dO P H) (compiledRows D dO P H)) := by
  have queryValid := QueryScanRow31SourcePlacement.transcript_row31_shape D H
    (compiledPublic D dO P H) (annotatedRun D dO P H).2.1.2 33 (by decide)
    i.m31 i.queryBytes i.state31 instanceFields.2.1 instanceFields.2.2.2.1
  obtain ⟨publicParsed, row31, row32, valid31, valid32⟩ := instanceFields
  obtain ⟨pairing, accumulator⟩ := D0TypedChecks.accepted_backend _ i typedAccepted
  exact HchecksReaderComposition.hchecks_partial
    (compiledPublic D dO P H) (compiledRows D dO P H) i.decoded i.data publicParsed
    (D0TypedChecks.accepted_matching _ i typedAccepted) pairing
    i.m31 i.queryBytes i.state31 i.m32 i.rho i.state32 row31 row32 valid31 valid32
    queryValid (D0TypedChecks.accepted_writer _ i typedAccepted) accumulator
    (D0TypedChecks.accepted_semantic _ i typedAccepted)

/-- Exact outstanding obligation for the admitted canonical instance.
It includes the check/data transfer, not just Rust execution equality. -/
def TypedBinding (D : LiteralByteProtocol.Decoder) (core : Decision) (P : Prover)
    (Q : Nat) (fallback : (Bytes → State) → SourceInputs) : Prop :=
  ∀ H : Bytes → State,
    ¬ RecordedBinaryExperimentBin.binaryCollision Q
      (eval H (recorded D (admit core) (R16CanonReduction.canon P))) →
    FS2.accepts (eval H (original D (admit core) (R16CanonReduction.canon P))) →
    D0TypedChecks.verify (compiledRows D (admit core) (R16CanonReduction.canon P) H)
      (source D core P fallback H) = true

theorem checked_acceptance (D : LiteralByteProtocol.Decoder) (core : Decision)
    (P : Prover) (Q : Nat) (fallback : (Bytes → State) → SourceInputs)
    (binding : TypedBinding D core P Q fallback) :
    OraclePortConsumer.CheckedAcceptance D (admit core) (R16CanonReduction.canon P) Q := by
  intro H hout ha
  exact Classical.choice (hchecks D (admit core) (R16CanonReduction.canon P) H
    (source D core P fallback H) (h_R16_instance D core P fallback H ha)
    (binding H hout ha))

#print axioms hchecks
#print axioms checked_acceptance
end AspisR1.OraclePortChecks
end
