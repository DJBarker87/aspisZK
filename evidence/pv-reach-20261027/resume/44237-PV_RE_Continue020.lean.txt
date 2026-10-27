import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue020
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.lift`.
Recursive calls remain the original extracted calls. -/
def continueAfter (x : aspis_core.field.M31) (out : Payload (aspis_core.field.CM31.from_m31 x)) : Result aspis_core.field.QM31 := do
  let c := out
  aspis_core.field.QM31.from_cm31 c

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (x : aspis_core.field.M31) :
    host_semantic.lift (x := x) =
      (aspis_core.field.CM31.from_m31 x >>= fun out => continueAfter (x := x) out) := by
  rw [host_semantic.lift]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (x : aspis_core.field.M31) (out : Payload (aspis_core.field.CM31.from_m31 x))
    (h : (aspis_core.field.CM31.from_m31 x) = .ok out) :
    host_semantic.lift (x := x) = continueAfter (x := x) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (x : aspis_core.field.M31) (e : Error)
    (h : (aspis_core.field.CM31.from_m31 x) = .fail e) :
    host_semantic.lift (x := x) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (x : aspis_core.field.M31)
    (h : (aspis_core.field.CM31.from_m31 x) = .div) :
    host_semantic.lift (x := x) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue020
