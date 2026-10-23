import Port3_Initial

/-! Literal emitted constructor body with its five external leaves installed.
The source span and declaration-normalization map are recorded by the source
checker. No template external axioms are imported. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_Constructor
open Aeneas Aeneas.Std Result VTop_Stages
open Port2_Initial

/-- Verbatim emitted core Result.map_err, with no external declaration. -/
def core.result.Result.map_err {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (self : core.result.Result T E) (op : O) :
    Result (core.result.Result T F) := do
  match self with
  | .Ok t => ok (.Ok t)
  | .Err e =>
    let t ← inst.call_once op e
    ok (.Err t)

structure Leaves (AllocError : Type) where
  finalLen : transport.Variant → Result Usize
  zero : Result KRaw
  copy : core.marker.Copy KRaw
  filled : core.marker.Copy KRaw → Usize → KRaw →
    Result (core.result.Result (alloc.vec.Vec KRaw) AllocError)
  zeroWide : Result ERaw
  one : Result KRaw

def allocationError {AllocError : Type} : core.ops.function.FnOnce Unit AllocError verifier.Error :=
  ⟨fun _ _ => ok (.Allocation)⟩

/-- Exact emitted instruction order, including map_err/branch/residual. -/
def extracted {AllocError : Type} (ops : Leaves AllocError) (v : transport.Variant) :
    Result (core.result.Result verifier.Accumulator verifier.Error) := do
  let i ← ops.finalLen v
  let q ← ops.zero
  let r ← ops.filled ops.copy i q
  let r1 ← core.result.Result.map_err allocationError r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let we ← ops.zeroWide
    let q1 ← ops.one
    ok (.Ok {weights := val, rhs := we, power := q1, next := 0#usize})
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      verifier.Accumulator (core.convert.FromSame verifier.Error) residual

theorem map_error_exact {AllocError : Type}
    (r : core.result.Result (alloc.vec.Vec KRaw) AllocError) :
    core.result.Result.map_err allocationError r () = Port3_Initial.mapFilled r := by
  cases r <;> rfl

theorem normalization {AllocError : Type} (ops : Leaves AllocError) (v : transport.Variant) :
    extracted ops v = Port3_Initial.emitted ops.finalLen ops.zero (ops.filled ops.copy)
      ops.zeroWide ops.one v := by
  simp only [extracted,Port3_Initial.emitted,map_error_exact]
  rfl

def leaves (reserved : Bool) : Leaves AspisR1Stage2.verifier.Error where
  finalLen := CheckpointBytes4Ops.finalLen
  zero := ok zeroK
  copy := {cloneInst := {clone := fun q => ok q}}
  filled := fun _ => CheckpointBytes3Allocation.filled reserved
  zeroWide := ok zeroE
  one := ok oneK

def installed (base : Ops) (reserved : Bool) : Ops :=
  {Port3_Initial.install base reserved with op12 := extracted (leaves reserved)}

theorem installed_constructor (base : Ops) (reserved : Bool) (v : transport.Variant) :
    (installed base reserved).op12 v = Port3_Initial.constructor reserved v :=
  normalization (leaves reserved) v

theorem initial_success (base : Ops) (reserved : Bool) (a : verifier.Accumulator)
    (accepted : (installed base reserved).op12 .S2 = ok (.Ok a)) :
    CheckpointBytes5Output.accumulator a = QueryAccumulator.initial := by
  rw [installed_constructor] at accepted
  exact Port3_Initial.accepted_initial base reserved a accepted

theorem allocation_rejects (base : Ops) :
    (installed base false).op12 .S2 = ok (.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Allocation) := by
  rw [installed_constructor]
  exact Port3_Initial.allocation_rejects base

#print axioms map_error_exact
#print axioms normalization
#print axioms installed_constructor
#print axioms initial_success
#print axioms allocation_rejects
end AspisR1.Port3_Constructor
end
