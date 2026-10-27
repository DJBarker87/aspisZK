import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue061
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.interpolation_basis_cell`.
Recursive calls remain the original extracted calls. -/
def continueAfter (basis : Array aspis_core.field.M31 28#usize) (k : Std.Usize) (j : Std.Usize) (out : Payload (host_sumcheck.interpolation_shift basis k)) : Result (Array aspis_core.field.M31 28#usize) := do
  let shifted := out
  let m ← Array.index_usize basis k
  let i ← Aeneas.Std.lift (UScalar.cast .U32 j)
  let m1 ← aspis_core.field.M31.mul m i
  let next ← aspis_core.field.M31.sub shifted m1
  Array.update basis k next

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (basis : Array aspis_core.field.M31 28#usize) (k : Std.Usize) (j : Std.Usize) :
    host_sumcheck.interpolation_basis_cell (basis := basis) (k := k) (j := j) =
      (host_sumcheck.interpolation_shift basis k >>= fun out => continueAfter (basis := basis) (k := k) (j := j) out) := by
  rw [host_sumcheck.interpolation_basis_cell]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (basis : Array aspis_core.field.M31 28#usize) (k : Std.Usize) (j : Std.Usize) (out : Payload (host_sumcheck.interpolation_shift basis k))
    (h : (host_sumcheck.interpolation_shift basis k) = .ok out) :
    host_sumcheck.interpolation_basis_cell (basis := basis) (k := k) (j := j) = continueAfter (basis := basis) (k := k) (j := j) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (basis : Array aspis_core.field.M31 28#usize) (k : Std.Usize) (j : Std.Usize) (e : Error)
    (h : (host_sumcheck.interpolation_shift basis k) = .fail e) :
    host_sumcheck.interpolation_basis_cell (basis := basis) (k := k) (j := j) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (basis : Array aspis_core.field.M31 28#usize) (k : Std.Usize) (j : Std.Usize)
    (h : (host_sumcheck.interpolation_shift basis k) = .div) :
    host_sumcheck.interpolation_basis_cell (basis := basis) (k := k) (j := j) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue061
