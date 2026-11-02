import PV_EVH_Runtime
import PV_EVH_OperatorFrames
set_option autoImplicit false
noncomputable section
namespace PV_EVH_RuntimeOperators
open Aeneas Aeneas.Std ProverRwFull PV_EVH_Runtime
variable [ExternalTypes]

structure Frames where
  invoke : ∀ {F A B : Type}, core.ops.function.FnOnce F A B → F → A → Q B
  drop : ∀ {F : Type}, F → Q Unit

structure Compatible (f : Frames) : Prop where
  invoke_view : ∀ {F A B : Type} (inst : core.ops.function.FnOnce F A B)
    (closure : F) (arg : A), PartialView (f.invoke inst closure arg) (inst.call_once closure arg)
  drop_view : ∀ {F : Type} (closure : F), PartialView (f.drop closure) (.ok ())

def map (f : Frames) {T E U F : Type} (inst : core.ops.function.FnOnce F T U)
    (r : core.result.Result T E) (closure : F) : Q (core.result.Result U E) :=
  match r with
  | .Ok value => do
    let out ← f.invoke inst closure value
    pure (.Ok out)
  | .Err e => do
    let _ ← f.drop closure
    pure (.Err e)

def mapErr (f : Frames) {T E F O : Type} (inst : core.ops.function.FnOnce O E F)
    (r : core.result.Result T E) (closure : O) : Q (core.result.Result T F) :=
  match r with
  | .Ok value => do
    let _ ← f.drop closure
    pure (.Ok value)
  | .Err e => do
    let out ← f.invoke inst closure e
    pure (.Err out)

theorem map_view (ops : ExternalFuns) (selected : PV_EVH_OperatorFrames.Selection ops)
    (f : Frames) (hf : Compatible f) {T E U F : Type}
    (inst : core.ops.function.FnOnce F T U) (r : core.result.Result T E) (closure : F) :
    PartialView (map f inst r closure) (ops.op11 inst r closure) := by
  rw [selected.map]
  cases r with
  | Ok value =>
    exact bind_view _ _ _ _ (hf.invoke_view inst closure value) (fun out => lift_view _)
  | Err e =>
    exact bind_view _ _ (.ok ()) (fun _ => .ok (core.result.Result.Err (T := U) e))
      (hf.drop_view closure) (fun _ => lift_view _)

theorem mapErr_view (ops : ExternalFuns) (selected : PV_EVH_OperatorFrames.Selection ops)
    (f : Frames) (hf : Compatible f) {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (r : core.result.Result T E) (closure : O) :
    PartialView (mapErr f inst r closure) (ops.op12 inst r closure) := by
  rw [selected.mapErr]
  cases r with
  | Ok value =>
    exact bind_view _ _ (.ok ()) (fun _ => .ok (core.result.Result.Ok (E := F) value))
      (hf.drop_view closure) (fun _ => lift_view _)
  | Err e =>
    exact bind_view _ _ _ _ (hf.invoke_view inst closure e) (fun out => lift_view _)

theorem unused_drop_fault (f : Frames) {T E U F : Type}
    (inst : core.ops.function.FnOnce F T U) (e : E) (closure : F)
    (w : State) (fault : Fault) (h : (f.drop closure w).outcome = .fault fault) :
    map f inst (.Err e) closure w =
      ⟨.fault fault,(f.drop closure w).state,(f.drop closure w).events⟩ :=
  bind_fault _ _ _ _ h

theorem callback_fault (f : Frames) {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (e : E) (closure : O)
    (w : State) (fault : Fault) (h : (f.invoke inst closure e w).outcome = .fault fault) :
    mapErr f inst (.Err (T := T) e) closure w =
      ⟨.fault fault,(f.invoke inst closure e w).state,(f.invoke inst closure e w).events⟩ :=
  bind_fault _ _ _ _ h

#print axioms map_view
#print axioms mapErr_view
#print axioms unused_drop_fault
#print axioms callback_fault
end PV_EVH_RuntimeOperators
