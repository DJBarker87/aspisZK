import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue013
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.boolean_point`.
Recursive calls remain the original extracted calls. -/
def continueAfter (row : Std.Usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (Array aspis_core.field.QM31 10#usize) := do
  let q := out
  let point := Array.repeat 10#usize q
  host_semantic.boolean_point_loop q row point 0#usize

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (row : Std.Usize) :
    host_semantic.boolean_point (row := row) =
      (aspis_core.field.QM31.ZERO >>= fun out => continueAfter (row := row) out) := by
  rw [host_semantic.boolean_point]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (row : Std.Usize) (out : Payload (aspis_core.field.QM31.ZERO))
    (h : (aspis_core.field.QM31.ZERO) = .ok out) :
    host_semantic.boolean_point (row := row) = continueAfter (row := row) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (row : Std.Usize) (e : Error)
    (h : (aspis_core.field.QM31.ZERO) = .fail e) :
    host_semantic.boolean_point (row := row) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (row : Std.Usize)
    (h : (aspis_core.field.QM31.ZERO) = .div) :
    host_semantic.boolean_point (row := row) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue013
