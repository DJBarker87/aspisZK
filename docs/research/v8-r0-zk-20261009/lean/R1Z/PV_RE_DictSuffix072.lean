import R1Z.PV_RE_DictSuffix071
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix072
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.derive_private_salt_step`.
Recursive calls remain the original extracted calls. -/
def continueAfter (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (tag : Std.U8) (index : Std.U32) (salts : alloc.vec.Vec (Array Std.U8 32#usize)) (out : Payload (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
      reserved hash context tag index)) : Result (core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
    verifier.Error) := do
  let r := out
  let r1 ←
    core.result.Result.map_err
      prover.derive_private_salt_step.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let salts1 ← alloc.vec.Vec.push salts val
    ok (core.result.Result.Ok salts1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec (Array Std.U8 32#usize)) (core.convert.FromSame
      verifier.Error) residual


end R1Z.PV_RE_DictSuffix072
pv_dict_congr ProverRwFull.prover.derive_private_salt_step
pv_dict_congr R1Z.PV_RE_DictSuffix072.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.prover.derive_private_salt_step
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix072.continueAfter
