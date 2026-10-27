import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue056
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.check_secure_column`.
Recursive calls remain the original extracted calls. -/
def continueAfter (column : Array aspis_core.field.QM31 1024#usize) (out : Payload (host_semantic.check_secure_column_loop column 0#usize)) : Result (core.result.Result Unit r1_wire.Error) := do
  let pending_return := out
  match pending_return with
  | none => ok (core.result.Result.Ok ())
  | some r => ok r

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (column : Array aspis_core.field.QM31 1024#usize) :
    host_semantic.check_secure_column (column := column) =
      (host_semantic.check_secure_column_loop column 0#usize >>= fun out => continueAfter (column := column) out) := by
  rw [host_semantic.check_secure_column]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (column : Array aspis_core.field.QM31 1024#usize) (out : Payload (host_semantic.check_secure_column_loop column 0#usize))
    (h : (host_semantic.check_secure_column_loop column 0#usize) = .ok out) :
    host_semantic.check_secure_column (column := column) = continueAfter (column := column) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (column : Array aspis_core.field.QM31 1024#usize) (e : Error)
    (h : (host_semantic.check_secure_column_loop column 0#usize) = .fail e) :
    host_semantic.check_secure_column (column := column) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (column : Array aspis_core.field.QM31 1024#usize)
    (h : (host_semantic.check_secure_column_loop column 0#usize) = .div) :
    host_semantic.check_secure_column (column := column) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue056
