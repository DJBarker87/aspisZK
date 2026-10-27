import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue034
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.opening_row`.
Recursive calls remain the original extracted calls. -/
def continueAfter (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gp : Array aspis_core.field.wide_exact.WideExact 29#usize) (row : Std.Usize) (out : Payload (aspis_core.field.wide_exact.WideExact.ZERO)) : Result aspis_core.field.wide_exact.WideExact := do
  let value := out
  prover.opening_row_loop coefficients gp row value 0#usize

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gp : Array aspis_core.field.wide_exact.WideExact 29#usize) (row : Std.Usize) :
    prover.opening_row (coefficients := coefficients) (gp := gp) (row := row) =
      (aspis_core.field.wide_exact.WideExact.ZERO >>= fun out => continueAfter (coefficients := coefficients) (gp := gp) (row := row) out) := by
  rw [prover.opening_row]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gp : Array aspis_core.field.wide_exact.WideExact 29#usize) (row : Std.Usize) (out : Payload (aspis_core.field.wide_exact.WideExact.ZERO))
    (h : (aspis_core.field.wide_exact.WideExact.ZERO) = .ok out) :
    prover.opening_row (coefficients := coefficients) (gp := gp) (row := row) = continueAfter (coefficients := coefficients) (gp := gp) (row := row) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gp : Array aspis_core.field.wide_exact.WideExact 29#usize) (row : Std.Usize) (e : Error)
    (h : (aspis_core.field.wide_exact.WideExact.ZERO) = .fail e) :
    prover.opening_row (coefficients := coefficients) (gp := gp) (row := row) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gp : Array aspis_core.field.wide_exact.WideExact 29#usize) (row : Std.Usize)
    (h : (aspis_core.field.wide_exact.WideExact.ZERO) = .div) :
    prover.opening_row (coefficients := coefficients) (gp := gp) (row := row) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue034
