import R1Z.PV_RDB2C_PV_RDB1_V181
import R1Z.PV_RDB2C_V258
import R1Z.PV_RDB2C_V259

section
namespace R1Z.PV_RDB2C_ResourceInstance
open Aeneas Aeneas.Std Result PV_RDB1_V183_ReserveWorld

def empty (T : Type) (address : Nat) : Buffer T := ⟨address,0,[],by rfl⟩

/-- Every layout/overflow guard precedes allocation. On the fixed 1024-element
WideExact buffer they pass under the target's public size bounds. -/
theorem materialize_request {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (width : shape.width=32)
    (wordBound : 1024≤wordMax) (byteBound : 32768≤byteMax)
    (address : Nat) (world : World S F) :
    native step wordMax byteMax shape (empty T address) 1024 world =
      finish step shape (empty T address) 1024 world := by
  have hw : ¬1024>wordMax := by omega
  have hb : ¬32768>byteMax := by omega
  simp only [native,growExact,empty,List.length_nil,Nat.sub_self,
    Nat.zero_add,width,show (1024:Nat)>0 by omega,show ¬(32=0) by omega,
    hw,show (1024:Nat)*32=32768 by rfl,hb,ite_true,ite_false]

/-- Native allocation failures retain the private allocator post-state, the
unchanged buffer and every initialized allocation. No successful-allocation
premise is imposed on the fixed public request. -/
theorem failed_request {T S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (address : Nat) (world : World S F) (state : S)
    (h : step ⟨address,0,1024,shape⟩ world.allocator=(none,state)) :
    (finish step shape (empty T address) 1024 world).buffer=empty T address ∧
    (finish step shape (empty T address) 1024 world).world.allocator=state ∧
    (finish step shape (empty T address) 1024 world).world.memory=world.memory ∧
    (finish step shape (empty T address) 1024 world).world.live=world.live := by
  have hh := allocation_error step shape (empty T address) 1024 world state h
  exact ⟨hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2⟩

theorem request_no_reallocation {S : Type}
    (allocate : core.alloc.layout.Layout → S → Option Nat × S)
    (reallocate : Nat → core.alloc.layout.Layout → Usize → S → Option Nat × S)
    (shape : Shape) (address : Nat) (state : S) :
    PV_RDB1_V183_ReservePrimitive.step allocate reallocate ⟨address,0,1024,shape⟩ state =
      allocate (PV_RDB1_V183_ReservePrimitive.layout shape 1024) state :=
  PV_RDB1_V183_ReservePrimitive.allocate_branch allocate reallocate _ state rfl

/-- Complete reserve/reference equality is inherited with allocation failure,
reallocation prefix and private world effects, not a returning-value-only law. -/
theorem reserve_complete {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (buffer : Buffer T)
    (additional : Nat) (world : World S F) :
    native step wordMax byteMax shape buffer additional world=
      reference step wordMax byteMax shape buffer additional world :=
  PV_RDB1_V183.complete step wordMax byteMax shape buffer additional world

theorem selected_layouts_padded : (32:Nat)%4=0 ∧ (2116:Nat)%4=0 := by decide

#print axioms selected_layouts_padded
#print axioms materialize_request
#print axioms failed_request
#print axioms request_no_reallocation
#print axioms reserve_complete
end R1Z.PV_RDB2C_ResourceInstance

end

section
namespace R1Z.PV_RDB2C_BoxAdequacy
open R1Z.PV_RDB2C_PublicRequests R1Z.PV_RDB2C_Box

/-- The retained runtime/allocator primitive adequacy law, stated at the
actual typed-object allocation boundary. Logical-object frame theorems alone
do not prove byte ranges disjoint or establish a valid Rust pointer. -/
def Adequate {T S : Type} (allocate : Request → S → Option Nat × S)
    (request : Request) (world : World T S) : Prop :=
  ∀ p state, allocate request world.allocator=(some p,state) →
    p≠0 ∧ p%request.alignment=0 ∧
    ∀ a, world.live a=true → a+request.size≤p ∨ p+request.size≤a

theorem initialized_fresh_aligned {T S : Type}
    (allocate : Request → S → Option Nat × S) (request : Request)
    (value : T) (world : World T S) (p : Nat) (state : S)
    (primitive_adequacy : Adequate allocate request world)
    (h : allocate request world.allocator=(some p,state)) :
    p≠0 ∧ p%request.alignment=0 ∧
    (lowered allocate request value world).2.objects p=some value ∧
    (∀ a, world.live a=true → a+request.size≤p ∨ p+request.size≤a) := by
  obtain ⟨nonnull,aligned,fresh⟩ := primitive_adequacy p state h
  exact ⟨nonnull,aligned,(initialized allocate request value world p state h).1,fresh⟩

theorem failure_has_no_initialization {T S : Type}
    (allocate : Request → S → Option Nat × S) (request : Request)
    (value : T) (world : World T S) (state : S)
    (h : allocate request world.allocator=(none,state)) :
    (lowered allocate request value world).2.objects=world.objects ∧
    (lowered allocate request value world).2.live=world.live := by
  simp only [lowered,h]

#print axioms initialized_fresh_aligned
#print axioms failure_has_no_initialization
end R1Z.PV_RDB2C_BoxAdequacy

end

section
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

end
