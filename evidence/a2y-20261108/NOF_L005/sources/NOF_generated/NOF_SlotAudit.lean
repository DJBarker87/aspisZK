import NNH_ExactRemainingTypes
import NNH_Tx2SlotTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOF_SlotAudit
open Lean Meta Elab

/-- The installed stage and SDK as functions of the residual seed `m`.
A slot whose weak-head value is still a projection of `m` is an UNINSTALLED
residual (in the literal host seed NNH_HostSeed.m0 such slots are `.div`). -/
def stageF (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
 (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) : VTop_Stages.Ops :=
 NNH_Tx2SlotTransport.stage m env err r
def sdkF (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
 (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) : AdapterRw.Ops :=
 NNH_CorrectConfiguration.sdk m env err r

partial def rootOf (e : Expr) : MetaM Expr := do
  match e with
  | .proj _ _ s => rootOf s
  | .mdata _ b => rootOf b
  | _ =>
    let f := e.getAppFn
    if let .const n _ := f then
      if let some info ← getProjectionFnInfo? n then
        let args := e.getAppArgs
        if h : info.numParams < args.size then return ← rootOf args[info.numParams]
    return e

run_meta do
  for (fn, sn) in [(``stageF, ``VTop_Stages.Ops), (``sdkF, ``AdapterRw.Ops)] do
    let info ← getConstInfo fn
    lambdaTelescope info.value! fun xs body => do
      let m := xs[0]!
      for f in getStructureFields (← getEnv) sn do
        let proj ← mkProjection body f
        let v ← whnf proj
        let root ← lambdaTelescope v fun _ b => rootOf b
        let residual := root == m
        let mentions := v.containsFVar m.fvarId!
        let head := (← lambdaTelescope v fun _ b => pure b.getAppFn.constName?)
        logInfo m!"SLOT {sn}.{f} residual={residual} mentions_m={mentions} head={head}"
end AspisR1.NOF_SlotAudit
end
