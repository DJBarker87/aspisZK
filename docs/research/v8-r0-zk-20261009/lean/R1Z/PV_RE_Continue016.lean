import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue016
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.extra`.
Recursive calls remain the original extracted calls. -/
def continueAfter (coefficients : Array aspis_core.field.QM31 1024#usize) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) (out : Payload (aspis_core.field.QM31.ZERO)) : Result aspis_core.field.QM31 := do
  let sum := out
  host_semantic.extra_loop0 sum coefficients a b sum 0#usize

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (coefficients : Array aspis_core.field.QM31 1024#usize) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) :
    host_semantic.extra (coefficients := coefficients) (a := a) (b := b) =
      (aspis_core.field.QM31.ZERO >>= fun out => continueAfter (coefficients := coefficients) (a := a) (b := b) out) := by
  rw [host_semantic.extra]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (coefficients : Array aspis_core.field.QM31 1024#usize) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) (out : Payload (aspis_core.field.QM31.ZERO))
    (h : (aspis_core.field.QM31.ZERO) = .ok out) :
    host_semantic.extra (coefficients := coefficients) (a := a) (b := b) = continueAfter (coefficients := coefficients) (a := a) (b := b) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (coefficients : Array aspis_core.field.QM31 1024#usize) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) (e : Error)
    (h : (aspis_core.field.QM31.ZERO) = .fail e) :
    host_semantic.extra (coefficients := coefficients) (a := a) (b := b) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (coefficients : Array aspis_core.field.QM31 1024#usize) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31)
    (h : (aspis_core.field.QM31.ZERO) = .div) :
    host_semantic.extra (coefficients := coefficients) (a := a) (b := b) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue016
