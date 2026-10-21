import OraclePortChecks

/-! Audit the exact data-producing frontier before using any parser witness.
The retained R16 instance predicate does not constrain its data field. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortDataChoiceDraft
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open RecordedBinaryExperimentBin (SourceInputs)
open RawCutTranscriptRun (ErasedPrefix)
open OraclePortExperiment (Decision)
open RawCutProverCompiler (Prover)
attribute [local irreducible] D0TypedChecks.verify MatchingSupport.match0 R15WriterModel.mismatched

def withData (i : SourceInputs) (data : MatchingSupport.Data LiteralTranscript.E) : SourceInputs :=
  { i with data := data }

theorem erased_fields_ignore_data (p : ErasedPrefix) (i : SourceInputs)
    (data : MatchingSupport.Data LiteralTranscript.E) :
    D0InstanceAdmission.Fields p (withData i data) ↔ D0InstanceAdmission.Fields p i := Iff.rfl

theorem compiled_fields_ignore_data (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) (i : SourceInputs)
    (data : MatchingSupport.Data LiteralTranscript.E) :
    OraclePortAdmission.InstanceFields D d P H (withData i data) ↔
      OraclePortAdmission.InstanceFields D d P H i := Iff.rfl

/-- A concrete counterexample schema: every mismatching replacement preserves
all R16 fields, but is rejected by the requested typed checker. No oracle,
parser or accepted frozen execution is postulated by this statement. -/
theorem fields_allow_rejected_data (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) (i : SourceInputs)
    (hi : OraclePortAdmission.InstanceFields D d P H i)
    (data : MatchingSupport.Data LiteralTranscript.E)
    (wrong : LiteralMatchingData.read (OraclePortAdmission.compiledRows D d P H) ≠ some data) :
    OraclePortAdmission.InstanceFields D d P H (withData i data) ∧
    D0TypedChecks.verify (OraclePortAdmission.compiledRows D d P H) (withData i data) ≠ true := by
  refine ⟨hi, ?_⟩
  intro accepted
  exact wrong (D0TypedChecks.accepted_matching _ _ accepted)

/-- Typed verification of two R16 witnesses forces their otherwise free data
to agree. The R16 field predicate alone cannot supply this equality. -/
theorem accepted_data_unique (rs : LiteralAcceptanceTerminal.TranscriptRounds)
    (i j : SourceInputs) (hi : D0TypedChecks.verify rs i = true)
    (hj : D0TypedChecks.verify rs j = true) : i.data = j.data := by
  exact Option.some.inj ((D0TypedChecks.accepted_matching rs i hi).symm.trans
    (D0TypedChecks.accepted_matching rs j hj))

/-- Isolated replacement for the concrete bad-writer attempt. The generic
R15 mismatched_no_match theorem supplies the badness law; keeping it abstract
prevents normalization of the concrete tower inside instance-field unification. -/
theorem r16_allows_bad_writer (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) (i : SourceInputs)
    (hi : OraclePortAdmission.InstanceFields D d P H i)
    (data : MatchingSupport.Data LiteralTranscript.E)
    (badness : ∀ x, ¬ MatchingSupport.match0 data x)
    (q : Fin 22 → Fin 262144) (hq : LiteralQueryRead.decode i.queryBytes = some q) :
    OraclePortAdmission.InstanceFields D d P H (withData i data) ∧
      D0TypedChecks.verify (OraclePortAdmission.compiledRows D d P H) (withData i data) ≠ true := by
  refine ⟨(compiled_fields_ignore_data D d P H i data).mpr hi, ?_⟩
  intro accepted
  have matched := D0TypedChecks.accepted_writer _ (withData i data) accepted q hq 0
  exact badness (q 0) matched

/-- A closed counterexample to universal typed acceptance from R16 fields:
one of i and i with c0 incremented is rejected, and both satisfy R16. This
changes one scalar field, avoiding the large concrete folding computation. -/
theorem r16_does_not_determine_typed_acceptance (D : LiteralByteProtocol.Decoder)
    (d : Decision) (P : Prover) (H : Bytes → State) (i : SourceInputs)
    (hi : OraclePortAdmission.InstanceFields D d P H i) :
    ∃ j : SourceInputs, OraclePortAdmission.InstanceFields D d P H j ∧
      D0TypedChecks.verify (OraclePortAdmission.compiledRows D d P H) j ≠ true := by
  by_cases accepted : D0TypedChecks.verify (OraclePortAdmission.compiledRows D d P H) i = true
  · let altered : MatchingSupport.Data LiteralTranscript.E := {i.data with c0 := i.data.c0 + 1}
    let j := withData i altered
    have hj : OraclePortAdmission.InstanceFields D d P H j :=
      (compiled_fields_ignore_data D d P H i altered).mpr hi
    refine ⟨j,hj,?_⟩
    intro other
    have eq := accepted_data_unique _ i j accepted other
    have scalar := congrArg (fun data : MatchingSupport.Data LiteralTranscript.E => data.c0) eq
    change i.data.c0 = i.data.c0 + 1 at scalar
    exact R15WriterModel.not_eq_add_one _ scalar
  · exact ⟨i,hi,accepted⟩

#print axioms erased_fields_ignore_data
#print axioms compiled_fields_ignore_data
#print axioms fields_allow_rejected_data
#print axioms accepted_data_unique
#print axioms r16_allows_bad_writer
#print axioms r16_does_not_determine_typed_acceptance
end AspisR1.OraclePortDataChoiceDraft
end
