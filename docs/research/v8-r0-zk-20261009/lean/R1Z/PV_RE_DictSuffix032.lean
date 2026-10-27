import R1Z.PV_RE_DictSuffix031
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix032
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


end R1Z.PV_RE_DictSuffix032
pv_dict_congr ProverRwFull.prover.opening_batch
pv_dict_congr R1Z.PV_RE_DictSuffix032.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.prover.opening_batch
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix032.continueAfter
