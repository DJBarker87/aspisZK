import OraclePortStoredAdmissionC4
import OraclePortReaderSourceDraft

/-! Stage (c) interface on the repaired carrier. R16 is construction-owned;
the remaining arithmetic/selected-reader implication is quoted explicitly.
No completed frozen-verifier claim follows merely from parser inhabitation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortStoredChecksC4
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
open RecordedBinaryExperimentBin (SourceInputs)
attribute [local instance] Classical.propDecidable

def source (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (fallback : (Bytes → State) → SourceInputs) (H : Bytes → State) : SourceInputs :=
  let base := if h : ∃ i, InstanceFields D (admitted d) (canon P) H i
    then Classical.choose h else fallback H
  OraclePortReaderSourceDraft.bindReader (rows D (admitted d) (canon P) H) base

theorem instance_ignores_data (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) (i : SourceInputs)
    (data : MatchingSupport.Data LiteralTranscript.E) :
    InstanceFields D d P H (OraclePortDataChoiceDraft.withData i data) ↔
      InstanceFields D d P H i := Iff.rfl

theorem source_instance (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (fallback : (Bytes → State) → SourceInputs) (H : Bytes → State)
    (ha : (eval H (original D (admitted d) (canon P))).2.2 = true) :
    InstanceFields D (admitted d) (canon P) H (source D d P fallback H) := by
  have hx := accepted_instance D d P H ha
  have hi := Classical.choose_spec hx
  unfold source
  rw [dif_pos hx]
  unfold OraclePortReaderSourceDraft.bindReader
  split <;> exact hi

theorem hchecks (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) (i : SourceInputs)
    (fields : InstanceFields D d P H i)
    (typed : D0TypedChecks.verify (rows D d P H) i = true) :
    Nonempty (LiteralAcceptanceTerminal.Checks (output D d P H).statement (rows D d P H)) := by
  have queryValid := QueryScanRow31SourcePlacement.transcript_row31_shape D H
    (output D d P H).statement (output D d P H).proof 33 (by decide)
    i.m31 i.queryBytes i.state31 fields.2.1 fields.2.2.2.1
  obtain ⟨publicParsed,row31,row32,valid31,valid32⟩ := fields
  obtain ⟨pairing,accumulator⟩ := D0TypedChecks.accepted_backend _ i typed
  exact HchecksReaderComposition.hchecks_partial _ _ i.decoded i.data publicParsed
    (D0TypedChecks.accepted_matching _ i typed) pairing
    i.m31 i.queryBytes i.state31 i.m32 i.rho i.state32 row31 row32 valid31 valid32
    queryValid (D0TypedChecks.accepted_writer _ i typed) accumulator
    (D0TypedChecks.accepted_semantic _ i typed)

def CheckedAcceptance (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (Q : Nat) : Type :=
  ∀ H : Bytes → State,
    ¬ RecordedBinaryExperimentBin.binaryCollision Q
      (view (eval H (annotated D d P))) →
    (eval H (original D d P)).2.2 = true →
    LiteralAcceptanceTerminal.Checks (output D d P H).statement (rows D d P H)

/-- Exact open obligation. This is not asserted for the multiproof kernel. -/
def ReaderBinding (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (Q : Nat) (fallback : (Bytes → State) → SourceInputs) : Prop :=
  ∀ H : Bytes → State,
    ¬ RecordedBinaryExperimentBin.binaryCollision Q
      (view (eval H (annotated D (admitted d) (canon P)))) →
    (eval H (original D (admitted d) (canon P))).2.2 = true →
    D0TypedChecks.verify (rows D (admitted d) (canon P) H)
      (source D d P fallback H) = true

def checked_acceptance (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (Q : Nat) (fallback : (Bytes → State) → SourceInputs)
    (binding : ReaderBinding D d P Q fallback) :
    CheckedAcceptance D (admitted d) (canon P) Q := by
  intro H clean accepted
  exact Classical.choice (hchecks D _ _ H _
    (source_instance D d P fallback H accepted) (binding H clean accepted))

/-- Visible R16 fields still cannot justify choosing arbitrary typed data.
Changing c0 preserves those fields but forces rejection of one candidate. -/
theorem fields_do_not_determine_typed_acceptance (D : LiteralByteProtocol.Decoder)
    (d : Decision) (P : Prover) (H : Bytes → State) (i : SourceInputs)
    (hi : InstanceFields D d P H i) :
    ∃ j : SourceInputs, InstanceFields D d P H j ∧
      D0TypedChecks.verify (rows D d P H) j ≠ true := by
  by_cases accepted : D0TypedChecks.verify (rows D d P H) i = true
  · let altered : MatchingSupport.Data LiteralTranscript.E := {i.data with c0 := i.data.c0 + 1}
    let j := OraclePortDataChoiceDraft.withData i altered
    refine ⟨j,hi,?_⟩
    intro other
    have eq := OraclePortDataChoiceDraft.accepted_data_unique _ i j accepted other
    have scalar := congrArg (fun data : MatchingSupport.Data LiteralTranscript.E => data.c0) eq
    change i.data.c0 = i.data.c0 + 1 at scalar
    exact R15WriterModel.not_eq_add_one _ scalar
  · exact ⟨i,hi,accepted⟩

#print axioms instance_ignores_data
#print axioms source_instance
#print axioms hchecks
#print axioms checked_acceptance
#print axioms fields_do_not_determine_typed_acceptance
end AspisR1.OraclePortStoredChecksC4
end
