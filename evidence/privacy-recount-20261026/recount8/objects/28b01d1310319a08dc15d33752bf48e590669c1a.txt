import R1Z.ProverRwOuterGuardBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwOuterMapErr
open Aeneas Aeneas.Std Result ProverRwFull

def map_err {T E F O : Type} (inst : core.ops.function.FnOnce O E F)
    (status : core.result.Result T E) (closure : O) : Result (core.result.Result T F) :=
  match status with
  | .Ok x => .ok (.Ok x)
  | .Err e => do
    let mapped ← inst.call_once closure e
    .ok (.Err mapped)

theorem source {T E F O : Type} (inst : core.ops.function.FnOnce O E F)
    (status : core.result.Result T E) (closure : O) :
    map_err inst status closure =
      ProverRwRngNativeBody.core.result.Result.map_err inst status closure := by
  cases status <;> rfl

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  ProverRwOuterGuardLeaves.selected {ops with op12 := @map_err}

theorem installed (ops : ExternalFuns) {T E F O : Type} (inst : core.ops.function.FnOnce O E F)
    (status : core.result.Result T E) (closure : O) :
    @core.result.Result.map_err _ (selected ops) T E F O inst status closure =
      map_err inst status closure := rfl

#print axioms source
#print axioms installed
end R1Z.ProverRwOuterMapErr
