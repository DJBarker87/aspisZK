import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue012
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.secure_coefficients`.
Recursive calls remain the original extracted calls. -/
def continueAfter (coefficients : Array aspis_core.field.wide_exact.WideExact 1024#usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (Array aspis_core.field.QM31 1024#usize) := do
  let q := out
  let out := Array.repeat 1024#usize q
  host_commitment.secure_coefficients_loop coefficients out 0#usize

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (coefficients : Array aspis_core.field.wide_exact.WideExact 1024#usize) :
    host_commitment.secure_coefficients (coefficients := coefficients) =
      (aspis_core.field.QM31.ZERO >>= fun out => continueAfter (coefficients := coefficients) out) := by
  rw [host_commitment.secure_coefficients]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (coefficients : Array aspis_core.field.wide_exact.WideExact 1024#usize) (out : Payload (aspis_core.field.QM31.ZERO))
    (h : (aspis_core.field.QM31.ZERO) = .ok out) :
    host_commitment.secure_coefficients (coefficients := coefficients) = continueAfter (coefficients := coefficients) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (coefficients : Array aspis_core.field.wide_exact.WideExact 1024#usize) (e : Error)
    (h : (aspis_core.field.QM31.ZERO) = .fail e) :
    host_commitment.secure_coefficients (coefficients := coefficients) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (coefficients : Array aspis_core.field.wide_exact.WideExact 1024#usize)
    (h : (aspis_core.field.QM31.ZERO) = .div) :
    host_commitment.secure_coefficients (coefficients := coefficients) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue012
