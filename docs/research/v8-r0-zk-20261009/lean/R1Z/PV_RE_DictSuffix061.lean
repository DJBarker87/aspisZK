import R1Z.PV_RE_DictSuffix060
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix061
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


end R1Z.PV_RE_DictSuffix061
pv_dict_congr ProverRwFull.host_sumcheck.interpolation_basis_cell
pv_dict_congr R1Z.PV_RE_DictSuffix061.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_sumcheck.interpolation_basis_cell
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix061.continueAfter
