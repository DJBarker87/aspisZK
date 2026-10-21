import OraclePortDataChoiceDraft

/-! A data-bound replacement for the underconstrained R16 source. This does
not assert that frozen acceptance passes the typed arithmetic checker. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortReaderSourceDraft
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open RawCutProverCompiler (Prover)
open OraclePortExperiment (Decision original recorded)
open OraclePortAdmission
open RecordedBinaryExperimentBin (SourceInputs)
open OraclePortDataChoiceDraft (withData)

/-- Preserve the R16 fields, but select data from the actual typed reader. -/
def bindReader (rs : LiteralAcceptanceTerminal.TranscriptRounds) (i : SourceInputs) : SourceInputs :=
  match LiteralMatchingData.read rs with
  | none => i
  | some data => withData i data

theorem instance_preserved (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) (i : SourceInputs)
    (hi : InstanceFields D d P H i) :
    InstanceFields D d P H (bindReader (compiledRows D d P H) i) := by
  unfold bindReader
  split <;> exact hi

theorem binding_weaker (rs : LiteralAcceptanceTerminal.TranscriptRounds) (i : SourceInputs)
    (hi : D0TypedChecks.verify rs i = true) :
    D0TypedChecks.verify rs (bindReader rs i) = true := by
  have hr := D0TypedChecks.accepted_matching rs i hi
  simpa only [bindReader,hr,withData] using hi

def readerSource (D : LiteralByteProtocol.Decoder) (core : Decision) (P : Prover)
    (fallback : (Bytes → State) → SourceInputs) (H : Bytes → State) : SourceInputs :=
  bindReader (compiledRows D (admit core) (R16CanonReduction.canon P) H)
    (source D core P fallback H)

/-- Quoted replacement frontier. Its source has a proved data-selection rule;
its acceptance-to-arithmetic implication is still an outstanding model proof. -/
def ReaderBinding (D : LiteralByteProtocol.Decoder) (core : Decision) (P : Prover)
    (Q : Nat) (fallback : (Bytes → State) → SourceInputs) : Prop :=
  ∀ H : Bytes → State,
    ¬ RecordedBinaryExperimentBin.binaryCollision Q
      (eval H (recorded D (admit core) (R16CanonReduction.canon P))) →
    FS2.accepts (eval H (original D (admit core) (R16CanonReduction.canon P))) →
    D0TypedChecks.verify (compiledRows D (admit core) (R16CanonReduction.canon P) H)
      (readerSource D core P fallback H) = true

theorem typed_binding_implies_reader_binding (D : LiteralByteProtocol.Decoder)
    (core : Decision) (P : Prover) (Q : Nat) (fallback : (Bytes → State) → SourceInputs)
    (h : OraclePortChecks.TypedBinding D core P Q fallback) :
    ReaderBinding D core P Q fallback := by
  intro H hout ha
  exact binding_weaker _ _ (h H hout ha)

def checked_acceptance (D : LiteralByteProtocol.Decoder) (core : Decision) (P : Prover)
    (Q : Nat) (fallback : (Bytes → State) → SourceInputs)
    (h : ReaderBinding D core P Q fallback) :
    OraclePortConsumer.CheckedAcceptance D (admit core) (R16CanonReduction.canon P) Q := by
  intro H hout ha
  exact Classical.choice (OraclePortChecks.hchecks D (admit core) (R16CanonReduction.canon P)
    H (readerSource D core P fallback H)
    (instance_preserved D (admit core) (R16CanonReduction.canon P) H _
      (h_R16_instance D core P fallback H ha)) (h H hout ha))

#print axioms instance_preserved
#print axioms binding_weaker
#print axioms typed_binding_implies_reader_binding
#print axioms checked_acceptance
end AspisR1.OraclePortReaderSourceDraft
end
