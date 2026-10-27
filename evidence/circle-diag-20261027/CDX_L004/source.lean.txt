import Lean
import RPx_Deployed
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let names : Array Name := #[
    `AspisR1CircleFallback.circle.secure_ood_circle_point_from_parameter,
    `AspisR1CircleFallback.transcript.CIRCLE_FALLBACK_PARAMETERS,
    `AspisR1CircleFallback.transcript.CIRCLE_FALLBACK_PARAMETERS.eq_1,
    `AspisR1CircleFallback.transcript.circle_fallback_point,
    `AspisR1CircleSampleWrapper.sampler.circle_sample,
    `AspisR1CircleSampleWrapper.sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint,
    `AspisR1CircleSampleWrapper.sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once,
    `AspisR1M31Inverse.field.M31.inv,
    `AspisR1M31Inverse.field.square_n,
    `AspisR1M31Inverse.field.square_n_loop,
    `AspisR1M31Inverse.field.square_n_loop.body,
    `AspisR64Field.field.M31.inv,
    `AspisR64Field.field.square_n,
    `AspisR64Field.field.square_n_loop,
    `AspisR64Field.field.square_n_loop.body,
    `AspisR65Field.field.M31.inv,
    `AspisR65Field.field.square_n,
    `AspisR65Field.field.square_n_loop,
    `AspisR65Field.field.square_n_loop.body,
    `AspisR66Field.field.M31.inv,
    `AspisR66Field.field.square_n,
    `AspisR66Field.field.square_n_loop,
    `AspisR66Field.field.square_n_loop.body,
    `AspisR72Sampler.circle.secure_circle_point_from_parameter,
    `AspisR72Sampler.circle.secure_ood_circle_point_from_parameter,
    `AspisR72Sampler.field.CM31.inv,
    `AspisR72Sampler.field.CM31.inv_with,
    `AspisR72Sampler.field.M31.inv,
    `AspisR72Sampler.field.QM31.try_inv,
    `AspisR72Sampler.field.square_n,
    `AspisR72Sampler.field.square_n_loop,
    `AspisR72Sampler.field.square_n_loop.body,
    `FIo_Native.aspis_core.field.QM31.pow,
    `FIo_Native.aspis_core.field.QM31.pow_loop,
    `FIo_Native.aspis_core.field.QM31.pow_loop.body,
    `V7Tag73CurrentHelpersOpaque.aspis_core.field.M31.inv,
    `V7Tag73CurrentHelpersOpaque.aspis_core.field.square_n,
    `V7Tag73CurrentHelpersOpaque.aspis_core.field.square_n_loop,
    `V7Tag73CurrentHelpersOpaque.aspis_core.field.square_n_loop.body,
    `circle.secure_ood_circle_point_from_parameter,
    `sampler.circle_sample.closure,
    `transcript.circle_fallback_point]
  for n in names do
    let some c := env.checked.get.find? n | throwError "missing constant {n}"
    let owner := match env.getModuleIdxFor? n with
      | some i => env.header.modules[i.toNat]!.module.toString
      | none => "current-or-builtin"
    logInfo m!"CDX_OWNER {(Json.mkObj [("name",toJson n.toString),("module",toJson owner),("type",toJson (repr c.type).pretty),("value",toJson (repr (c.value? true)).pretty)]).compress}"
  for m in env.header.modules do
    if m.module.toString.startsWith "XRk" || m.module.toString.startsWith "XRn" then
      throwError "worker module imported {m.module}"
  logInfo "CDX_NO_WORKER_IMPORTS"
