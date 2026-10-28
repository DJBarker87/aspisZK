import R1Z.PV_RDB2C_ResourceInstance
import R1Z.PV_RDB2C_BoxAdequacy
namespace R1Z.PV_RDB2C_PrimitiveResults
open Aeneas Aeneas.Std Result PV_RDB2C_PublicRequests

def materialize {S : Type} (allocate : Request → S → Result (Option Nat × S))
    (w : PV_B2_251c1.host_weights.Weights) (kappa : PV_B2_C_MutationStep.E)
    (world : PV_RDB2C_V258.World S) := do
  let decision ← allocate PV_RDB2C_V258.request world.allocator
  ok (PV_RDB2C_V258.copied (fun _ _ => decision) w kappa world)

def materializeReference {S : Type} (allocate : Request → S → Result (Option Nat × S))
    (w : PV_B2_251c1.host_weights.Weights) (kappa : PV_B2_C_MutationStep.E)
    (world : PV_RDB2C_V258.World S) := do
  let decision ← allocate PV_RDB2C_V258.request world.allocator
  ok (PV_RDB2C_V258.original (fun _ _ => decision) w kappa world)

theorem materialize_complete {S : Type} (allocate : Request → S → Result (Option Nat × S))
    (w : PV_B2_251c1.host_weights.Weights) (kappa : PV_B2_C_MutationStep.E)
    (world : PV_RDB2C_V258.World S) :
    materialize allocate w kappa world=materializeReference allocate w kappa world := by
  unfold materialize materializeReference
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro decision _
  rw [PV_RDB2C_V258.complete]

def boxed {S : Type} (allocate : Request → S → Result (Option Nat × S))
    (v : PV_B2_C_WeightsNative.transport.Variant)
    (alpha : Array PV_B2_C_ConstructorRows.K 10#usize)
    (z : Array PV_B2_C_ConstructorRows.Point 2#usize) (world : PV_RDB2C_V259.World S) := do
  let r ← PV_B2_C_WeightsNative.host_weights.Weights.new v alpha z
  match r with
  | .Err e => ok (PV_RDB2C_V259.finish (fun _ _ => (none,world.allocator)) (.Err e) world)
  | .Ok value => do
    let decision ← allocate PV_RDB2C_V259.request world.allocator
    ok (PV_RDB2C_V259.finish (fun _ _ => decision) (.Ok value) world)

def boxedReference {S : Type} (allocate : Request → S → Result (Option Nat × S))
    (v : PV_B2_C_WeightsNative.transport.Variant)
    (alpha : Array PV_B2_C_ConstructorRows.K 10#usize)
    (z : Array PV_B2_C_ConstructorRows.Point 2#usize) (world : PV_RDB2C_V259.World S) := do
  let r ← PV_B2_C_ConstructorSuccess.staged v alpha z
  match r with
  | .Err e => ok (PV_RDB2C_V259.finish (fun _ _ => (none,world.allocator)) (.Err e) world)
  | .Ok value => do
    let decision ← allocate PV_RDB2C_V259.request world.allocator
    ok (PV_RDB2C_V259.finish (fun _ _ => decision) (.Ok value) world)

theorem boxed_complete {S : Type} (allocate : Request → S → Result (Option Nat × S))
    (v : PV_B2_C_WeightsNative.transport.Variant)
    (alpha : Array PV_B2_C_ConstructorRows.K 10#usize)
    (z : Array PV_B2_C_ConstructorRows.Point 2#usize) (world : PV_RDB2C_V259.World S) :
    boxed allocate v alpha z world=boxedReference allocate v alpha z world := by
  unfold boxed boxedReference
  rw [PV_B2_C_ConstructorSuccess.new_eq_staged]

theorem materialize_primitive_failure {S : Type}
    (allocate : Request → S → Result (Option Nat × S)) (e : Error)
    (w : PV_B2_251c1.host_weights.Weights) (kappa : PV_B2_C_MutationStep.E)
    (world : PV_RDB2C_V258.World S)
    (h : allocate PV_RDB2C_V258.request world.allocator=fail e) :
    materialize allocate w kappa world=fail e := by simp only [materialize,h,bind_tc_fail]

theorem materialize_primitive_divergence {S : Type}
    (allocate : Request → S → Result (Option Nat × S))
    (w : PV_B2_251c1.host_weights.Weights) (kappa : PV_B2_C_MutationStep.E)
    (world : PV_RDB2C_V258.World S)
    (h : allocate PV_RDB2C_V258.request world.allocator=div) :
    materialize allocate w kappa world=div := by simp only [materialize,h,bind_tc_div]

/-- Apply the same actual abort/error handler to the entire returned state.
The handler can fail, diverge or change runtime state; no success is assumed. -/
theorem boxed_with_handlers {S R : Type}
    (allocate : Request → S → Result (Option Nat × S))
    (v : PV_B2_C_WeightsNative.transport.Variant)
    (alpha : Array PV_B2_C_ConstructorRows.K 10#usize)
    (z : Array PV_B2_C_ConstructorRows.Point 2#usize) (world : PV_RDB2C_V259.World S)
    (handler : PV_RDB2C_V259.Returned × PV_RDB2C_V259.World S → Result R) :
    (boxed allocate v alpha z world >>= handler) =
      (boxedReference allocate v alpha z world >>= handler) :=
  congrArg (fun r => r >>= handler) (boxed_complete allocate v alpha z world)

#print axioms boxed_with_handlers
#print axioms materialize_complete
#print axioms boxed_complete
#print axioms materialize_primitive_failure
#print axioms materialize_primitive_divergence
end R1Z.PV_RDB2C_PrimitiveResults
