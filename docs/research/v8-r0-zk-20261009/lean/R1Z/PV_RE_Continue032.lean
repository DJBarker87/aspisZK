import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue032
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.opening_batch`.
Recursive calls remain the original extracted calls. -/
def continueAfter (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact) (out : Payload (weights.powers 29#usize gamma)) : Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact) := do
  let gp := out
  let q :=
    alloc.vec.Vec.with_capacity aspis_core.field.wide_exact.WideExact
      1024#usize
  prover.opening_batch_loop coefficients gp q 0#usize

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact) :
    prover.opening_batch (coefficients := coefficients) (gamma := gamma) =
      (weights.powers 29#usize gamma >>= fun out => continueAfter (coefficients := coefficients) (gamma := gamma) out) := by
  rw [prover.opening_batch]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact) (out : Payload (weights.powers 29#usize gamma))
    (h : (weights.powers 29#usize gamma) = .ok out) :
    prover.opening_batch (coefficients := coefficients) (gamma := gamma) = continueAfter (coefficients := coefficients) (gamma := gamma) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact) (e : Error)
    (h : (weights.powers 29#usize gamma) = .fail e) :
    prover.opening_batch (coefficients := coefficients) (gamma := gamma) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact)
    (h : (weights.powers 29#usize gamma) = .div) :
    prover.opening_batch (coefficients := coefficients) (gamma := gamma) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue032
