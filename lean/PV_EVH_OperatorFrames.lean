import PV_EVH_ResultOps
set_option autoImplicit false
noncomputable section
namespace PV_EVH_OperatorFrames
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes]

/-- Native invocation and unused closure destruction are computations, not
Results evaluated before the operator. Argument/capture destruction on the
invoked branch belongs to invoke, including its failure/unwind paths. -/
structure Frames where
  invoke : ∀ {F A B : Type}, core.ops.function.FnOnce F A B → F → A → P B
  drop : ∀ {F : Type}, F → P Unit

structure Compatible (f : Frames) : Prop where
  invoke_fixed : ∀ {F A B : Type} (inst : core.ops.function.FnOnce F A B)
    (closure : F) (arg : A), FinishedView (f.invoke inst closure arg) (inst.call_once closure arg)
  drop_fixed : ∀ {F : Type} (closure : F), FinishedView (f.drop closure) (.ok ())

/-- Source selection is explicit at the consuming dictionary. It is a P
obligation, never a replacement dictionary or an added trust item. -/
structure Selection (ops : ExternalFuns) : Prop where
  map : ∀ {T E U F : Type} (inst : core.ops.function.FnOnce F T U)
    (r : core.result.Result T E) (closure : F),
    ops.op11 inst r closure = PV_EVH_ResultOps.sourceMap inst r closure
  mapErr : ∀ {T E F O : Type} (inst : core.ops.function.FnOnce O E F)
    (r : core.result.Result T E) (closure : O),
    ops.op12 inst r closure = PV_EVH_ResultOps.sourceMapErr inst r closure

def map (f : Frames) {T E U F : Type} (inst : core.ops.function.FnOnce F T U)
    (r : core.result.Result T E) (closure : F) : P (core.result.Result U E) :=
  PV_EVH_ResultOps.map (f.invoke inst closure) (f.drop closure) r

def mapErr (f : Frames) {T E F O : Type} (inst : core.ops.function.FnOnce O E F)
    (r : core.result.Result T E) (closure : O) : P (core.result.Result T F) :=
  PV_EVH_ResultOps.mapErr (f.invoke inst closure) (f.drop closure) r

theorem map_fixed (ops : ExternalFuns) (selected : Selection ops)
    (f : Frames) (compatible : Compatible f) {T E U F : Type}
    (inst : core.ops.function.FnOnce F T U) (r : core.result.Result T E) (closure : F) :
    FinishedView (map f inst r closure) (ops.op11 inst r closure) := by
  rw [selected.map]
  exact PV_EVH_ResultOps.map_fixed ops inst closure _ _
    (compatible.invoke_fixed inst closure) (compatible.drop_fixed closure) r

theorem mapErr_fixed (ops : ExternalFuns) (selected : Selection ops)
    (f : Frames) (compatible : Compatible f) {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (r : core.result.Result T E) (closure : O) :
    FinishedView (mapErr f inst r closure) (ops.op12 inst r closure) := by
  rw [selected.mapErr]
  exact PV_EVH_ResultOps.mapErr_fixed ops inst closure _ _
    (compatible.invoke_fixed inst closure) (compatible.drop_fixed closure) r

/-- On an unused-closure branch, the complete drop prefix is retained. -/
theorem map_error_run (f : Frames) {T E U F : Type}
    (inst : core.ops.function.FnOnce F T U) (e : E) (closure : F) :
    map f inst (.Err e) closure =
      PV_EVH_Prefix.bind (f.drop closure) (fun _ =>
        PV_EVH_Prefix.lift (.ok (core.result.Result.Err (T := U) e))) := rfl

theorem mapErr_ok_run (f : Frames) {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (value : T) (closure : O) :
    mapErr f inst (.Ok value) closure =
      PV_EVH_Prefix.bind (f.drop closure) (fun _ =>
        PV_EVH_Prefix.lift (.ok (core.result.Result.Ok (E := F) value))) := rfl
#print axioms map_fixed
#print axioms mapErr_fixed
#print axioms map_error_run
#print axioms mapErr_ok_run
end PV_EVH_OperatorFrames
