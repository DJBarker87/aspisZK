import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix004
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


end R1Z.PV_RE_ComposedSuffix004
pv_composed_source_contexts ProverRwFull.aspis_prover.state_only_entropy.sync_directory
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix004.continueAfter
