import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue022
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.interpolate`.
Recursive calls remain the original extracted calls. -/
def continueAfter (values : Array aspis_core.field.QM31 28#usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (Array aspis_core.field.QM31 28#usize) := do
  let q := out
  let out := Array.repeat 28#usize q
  host_sumcheck.interpolate_loop values out 0#usize

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (values : Array aspis_core.field.QM31 28#usize) :
    host_sumcheck.interpolate (values := values) =
      (aspis_core.field.QM31.ZERO >>= fun out => continueAfter (values := values) out) := by
  rw [host_sumcheck.interpolate]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (values : Array aspis_core.field.QM31 28#usize) (out : Payload (aspis_core.field.QM31.ZERO))
    (h : (aspis_core.field.QM31.ZERO) = .ok out) :
    host_sumcheck.interpolate (values := values) = continueAfter (values := values) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (values : Array aspis_core.field.QM31 28#usize) (e : Error)
    (h : (aspis_core.field.QM31.ZERO) = .fail e) :
    host_sumcheck.interpolate (values := values) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (values : Array aspis_core.field.QM31 28#usize)
    (h : (aspis_core.field.QM31.ZERO) = .div) :
    host_sumcheck.interpolate (values := values) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue022
