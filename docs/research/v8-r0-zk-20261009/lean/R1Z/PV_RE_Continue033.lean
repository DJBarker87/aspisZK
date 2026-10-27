import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue033
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.opening_inactive`.
Recursive calls remain the original extracted calls. -/
def continueAfter (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights) (out : Payload (aspis_core.field.wide_exact.WideExact.ZERO)) : Result aspis_core.field.wide_exact.WideExact := do
  let inactive := out
  prover.opening_inactive_loop q w inactive 0#usize

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights) :
    prover.opening_inactive (q := q) (w := w) =
      (aspis_core.field.wide_exact.WideExact.ZERO >>= fun out => continueAfter (q := q) (w := w) out) := by
  rw [prover.opening_inactive]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights) (out : Payload (aspis_core.field.wide_exact.WideExact.ZERO))
    (h : (aspis_core.field.wide_exact.WideExact.ZERO) = .ok out) :
    prover.opening_inactive (q := q) (w := w) = continueAfter (q := q) (w := w) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights) (e : Error)
    (h : (aspis_core.field.wide_exact.WideExact.ZERO) = .fail e) :
    prover.opening_inactive (q := q) (w := w) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights)
    (h : (aspis_core.field.wide_exact.WideExact.ZERO) = .div) :
    prover.opening_inactive (q := q) (w := w) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue033
