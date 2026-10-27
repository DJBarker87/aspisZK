import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue004
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

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (directory : std.path.Path) :
    aspis_prover.state_only_entropy.sync_directory (directory := directory) =
      (std.fs.File.open (Shared0T.Insts.CoreConvertAsRef
      std.path.Path.Insts.CoreConvertAsRefPath) directory >>= fun out => continueAfter (directory := directory) out) := by
  rw [aspis_prover.state_only_entropy.sync_directory]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (directory : std.path.Path) (out : Payload (std.fs.File.open (Shared0T.Insts.CoreConvertAsRef
      std.path.Path.Insts.CoreConvertAsRefPath) directory))
    (h : (std.fs.File.open (Shared0T.Insts.CoreConvertAsRef
      std.path.Path.Insts.CoreConvertAsRefPath) directory) = .ok out) :
    aspis_prover.state_only_entropy.sync_directory (directory := directory) = continueAfter (directory := directory) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (directory : std.path.Path) (e : Error)
    (h : (std.fs.File.open (Shared0T.Insts.CoreConvertAsRef
      std.path.Path.Insts.CoreConvertAsRefPath) directory) = .fail e) :
    aspis_prover.state_only_entropy.sync_directory (directory := directory) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (directory : std.path.Path)
    (h : (std.fs.File.open (Shared0T.Insts.CoreConvertAsRef
      std.path.Path.Insts.CoreConvertAsRefPath) directory) = .div) :
    aspis_prover.state_only_entropy.sync_directory (directory := directory) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue004
