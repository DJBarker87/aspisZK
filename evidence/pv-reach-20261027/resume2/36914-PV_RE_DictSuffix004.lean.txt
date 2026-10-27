import R1Z.PV_RE_DictSuffix003
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix004
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_entropy.sync_directory`.
Recursive calls remain the original extracted calls. -/
def continueAfter (directory : std.path.Path) (out : Payload (std.fs.File.open (Shared0T.Insts.CoreConvertAsRef
      std.path.Path.Insts.CoreConvertAsRefPath) directory)) : Result (core.result.Result Unit std.io.error.Error) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val => std.fs.File.sync_all val
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame std.io.error.Error) residual


end R1Z.PV_RE_DictSuffix004
pv_dict_congr ProverRwFull.aspis_prover.state_only_entropy.sync_directory
pv_dict_congr R1Z.PV_RE_DictSuffix004.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.aspis_prover.state_only_entropy.sync_directory
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix004.continueAfter
