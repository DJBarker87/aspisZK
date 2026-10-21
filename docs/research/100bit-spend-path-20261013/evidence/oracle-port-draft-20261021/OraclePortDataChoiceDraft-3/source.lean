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

/-- The counterexample needs no assumption about a failing reader: replacing
V by fold(W)+1 breaks every first match while preserving every R16 field. -/
theorem r16_allows_bad_writer (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) (i : SourceInputs)
    (hi : OraclePortAdmission.InstanceFields D d P H i)
    (q : Fin 22 → Fin 262144) (hq : LiteralQueryRead.decode i.queryBytes = some q) :
    ∃ bad : SourceInputs,
      OraclePortAdmission.InstanceFields D d P H bad ∧
      bad.queryBytes = i.queryBytes ∧
      D0TypedChecks.verify (OraclePortAdmission.compiledRows D d P H) bad = false := by
  let bad := withData i (R15WriterModel.mismatched i.data)
  refine ⟨bad, hi, rfl, Bool.eq_false_iff.mpr ?_⟩
  intro accepted
  have matched := D0TypedChecks.accepted_writer _ bad accepted q hq 0
  exact R15WriterModel.mismatched_no_match i.data (q 0) matched

#print axioms erased_fields_ignore_data
#print axioms compiled_fields_ignore_data
#print axioms fields_allow_rejected_data
#print axioms accepted_data_unique
#print axioms r16_allows_bad_writer
end AspisR1.OraclePortDataChoiceDraft
end
