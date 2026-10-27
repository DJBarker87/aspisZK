import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue023
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.interpolation_basis`.
Recursive calls remain the original extracted calls. -/
def continueAfter (i : Std.Usize) (out : Payload (aspis_core.field.M31.ZERO)) : Result ((Array aspis_core.field.M31 28#usize) × aspis_core.field.M31) := do
  let m := out
  let basis := Array.repeat 28#usize m
  let m1 ← aspis_core.field.M31.ONE
  let basis1 ← Array.update basis 0#usize m1
  host_sumcheck.interpolation_basis_steps basis1 m1 0#usize i 0#usize

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (i : Std.Usize) :
    host_sumcheck.interpolation_basis (i := i) =
      (aspis_core.field.M31.ZERO >>= fun out => continueAfter (i := i) out) := by
  rw [host_sumcheck.interpolation_basis]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (i : Std.Usize) (out : Payload (aspis_core.field.M31.ZERO))
    (h : (aspis_core.field.M31.ZERO) = .ok out) :
    host_sumcheck.interpolation_basis (i := i) = continueAfter (i := i) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (i : Std.Usize) (e : Error)
    (h : (aspis_core.field.M31.ZERO) = .fail e) :
    host_sumcheck.interpolation_basis (i := i) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (i : Std.Usize)
    (h : (aspis_core.field.M31.ZERO) = .div) :
    host_sumcheck.interpolation_basis (i := i) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue023
