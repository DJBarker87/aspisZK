import R1Z.ProverRwSuccessBodyInterpretation
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessHeapSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Global := Unit
abbrev aspis_core.r0.heap.filled.closure (T : Type) := Unit
def
  aspis_core.r0.heap.filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError.call_once
  {T : Type} (coremarkerCopyInst : core.marker.Copy T)
  (c : aspis_core.r0.heap.filled.closure T)
  (tupled_args : alloc.collections.TryReserveError) :
  Result aspis_core.r0.Error
  := do
  ok aspis_core.r0.Error.Allocation

def
  aspis_core.r0.heap.filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError
  {T : Type} (coremarkerCopyInst : core.marker.Copy T) :
  core.ops.function.FnOnce (aspis_core.r0.heap.filled.closure T)
  alloc.collections.TryReserveError aspis_core.r0.Error := {
  call_once :=
    aspis_core.r0.heap.filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError.call_once
    coremarkerCopyInst
}

def aspis_core.r0.heap.filled
  {T : Type} (coremarkerCopyInst : core.marker.Copy T) (n : Std.Usize)
  (value : T) :
  Result (core.result.Result (alloc.vec.Vec T) aspis_core.r0.Error)
  := do
  let (r, out) ←
    alloc.vec.Vec.try_reserve_exact Global (alloc.vec.Vec.new T) n
  let r1 ←
    core.result.Result.map_err
      (aspis_core.r0.heap.filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError
      coremarkerCopyInst) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let out1 ← alloc.vec.Vec.resize coremarkerCopyInst.cloneInst out n value
    ok (core.result.Result.Ok out1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec T) (core.convert.FromSame aspis_core.r0.Error) residual
end R1Z.ProverRwSuccessHeapSource
