import PV_STX_NonceWorld
import PV_STX_DenoteRules
set_option autoImplicit false
noncomputable section
namespace PV_STX_NonceSync
open Aeneas Aeneas.Std ProverRwFull PV_STX_Code PV_STX_Machine PV_STX_DenoteRules
open PV_STX_NonceWorld (Request)
variable [ExternalTypes] [ExternalFuns]

def fixed : {X : Type} → Request X → Result X
  | _,.writeAll file bytes => std.fs.File.Insts.StdIoWrite.write_all file bytes
  | _,.sync file => std.fs.File.sync_all file
  | _,.openFile convert path => std.fs.File.open convert path
  | _,.optionsOpen convert options path => std.fs.OpenOptions.open convert options path

def syncDirectory (directory : std.path.Path) : Code Request (core.result.Result Unit std.io.error.Error) := do
  let r ← Code.call (.openFile (Shared0T.Insts.CoreConvertAsRef
      std.path.Path.Insts.CoreConvertAsRefPath) directory)
  let cf ← Code.result (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue file => Code.call (.sync file)
  | core.ops.control_flow.ControlFlow.Break residual =>
    Code.result (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame std.io.error.Error) residual)

theorem erases (directory : std.path.Path) :
    denote fixed (syncDirectory directory) = aspis_prover.state_only_entropy.sync_directory directory := by
  simp only [syncDirectory,aspis_prover.state_only_entropy.sync_directory,
    bind_rule,call_rule,result_rule,fixed]
  simp only [Bind.bind,Aeneas.Std.bind]
  repeat first | rfl | split

/-- Actual source suffix: directory sync receives the file and world returned
by open. Includes every complete Result of sync, without a supplied callee run. -/
theorem opened_then_sync {W E : Type} (handler : Handler Request W E)
    (directory : std.path.Path) (file : std.fs.File) (w : W)
    (r : Result (core.result.Result Unit std.io.error.Error))
    (ho : (handler (.openFile (Shared0T.Insts.CoreConvertAsRef
       std.path.Path.Insts.CoreConvertAsRefPath) directory) w).answer = .returned (.ok (.Ok file)))
    (hs : (handler (.sync file) (handler (.openFile (Shared0T.Insts.CoreConvertAsRef
       std.path.Path.Insts.CoreConvertAsRefPath) directory) w).world).answer = .returned r) :
    let first := handler (.openFile (Shared0T.Insts.CoreConvertAsRef
      std.path.Path.Insts.CoreConvertAsRefPath) directory) w
    let second := handler (.sync file) first.world
    run handler 5 (syncDirectory directory) w =
      ⟨.returned r,second.world,first.events ++ second.events⟩ := by
  cases r <;> simp only [syncDirectory,Bind.bind,Pure.pure,run,advance,start,step,
    resumed,continueWith,ho,hs,core.result.Result.Insts.CoreOpsTry.branch,
    List.nil_append,List.append_nil]

#print axioms erases
#print axioms opened_then_sync
end PV_STX_NonceSync
