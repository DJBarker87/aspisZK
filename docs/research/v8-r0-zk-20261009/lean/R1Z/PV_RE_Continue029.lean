import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue029
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.fixed_k_column`.
Recursive calls remain the original extracted calls. -/
def continueAfter (values : Slice aspis_core.field.QM31) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (Array aspis_core.field.QM31 1024#usize) := do
  let q := out
  let out := Array.repeat 1024#usize q
  prover.fixed_k_column_loop values out 0#usize

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (values : Slice aspis_core.field.QM31) :
    prover.fixed_k_column (values := values) =
      (aspis_core.field.QM31.ZERO >>= fun out => continueAfter (values := values) out) := by
  rw [prover.fixed_k_column]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (values : Slice aspis_core.field.QM31) (out : Payload (aspis_core.field.QM31.ZERO))
    (h : (aspis_core.field.QM31.ZERO) = .ok out) :
    prover.fixed_k_column (values := values) = continueAfter (values := values) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (values : Slice aspis_core.field.QM31) (e : Error)
    (h : (aspis_core.field.QM31.ZERO) = .fail e) :
    prover.fixed_k_column (values := values) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (values : Slice aspis_core.field.QM31)
    (h : (aspis_core.field.QM31.ZERO) = .div) :
    prover.fixed_k_column (values := values) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue029
