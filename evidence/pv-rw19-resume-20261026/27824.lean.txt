import R1Z.ProverRw19MathematicalLength
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19PreparedAssembly
open Aeneas Aeneas.Std Result ProverRwFull
-- Data only. No correspondence laws or successful-run premises are fields.
abbrev Prepared := ProverCommitFront46.Fields ×
  List ProverCommitPublish43.QueryParts × List ProverCommitPublish43.Slot
abbrev Preparation := Result (core.result.Result Prepared verifier.Error)

-- A mathematical preparation stage must still be constructed for the deployed
-- caller. Its errors/failure/divergence are preserved, never replaced by bytes.
def proofBytes (preparation : Preparation) : Result ProverRw19AuditData.ByteStatus := do
  let status ← preparation
  match status with
  | .Err error => ok (.Err error)
  | .Ok (fields,queries,slots) => ProverRw19MathematicalAssembly.proofBytes fields queries slots

def output (preparation : Preparation) : Result ProverRw19AuditValue.Status :=
  ProverRw19AuditData.attachAudit (proofBytes preparation)

theorem failure (error : Aeneas.Std.Error) : proofBytes (.fail error) = .fail error := rfl
theorem divergence : proofBytes .div = .div := rfl
theorem rejected (error : verifier.Error) : proofBytes (.ok (.Err error)) = .ok (.Err error) := rfl

theorem length (preparation : Preparation) : ProverRw19ByteLength.HasLength 57607 (proofBytes preparation) := by
  cases preparation with
  | fail error => trivial
  | div => trivial
  | ok status =>
    cases status with
    | Err error => trivial
    | Ok prepared =>
      rcases prepared with ⟨fields,queries,slots⟩
      exact ProverRw19MathematicalLength.proof fields queries slots

#print axioms proofBytes
#print axioms output
#print axioms failure
#print axioms divergence
#print axioms rejected
#print axioms length
end R1Z.ProverRw19PreparedAssembly
