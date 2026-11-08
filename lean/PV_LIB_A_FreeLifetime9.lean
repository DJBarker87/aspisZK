import PV_LIB_A_WeakFreeFacts9
import PV_LIB_A_ProviderBacking9
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_FreeLifetime9
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner
open PV_LIB_StoreActionTable

/-- The earlier source-only suffix does not perform an OWNER free. Even when
it clears the source root, the supplied world's live flag stays unchanged.
This is a checked model gap, not a counterexample to Rust Weak::drop. -/
theorem old_world_unchanged (C : Carrier OWNER Data) (c : Config) (w : OWNER)
    (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (a i pointer : Nat) (unit : Data) :
    (sourceReceive C c es stack site (.deallocate ⟨a,i,[]⟩)
      ⟨.returned (.ok unit),w,events⟩).base.current.world.world.live pointer =
        w.world.live pointer := by
  change (PV_THR2_ChildBoundary.delivered C {c with store := write c.store ⟨a,i,[]⟩ none}
    site.waiting ⟨.returned (.ok unit),w,events⟩).world.world.live pointer = _
  exact congrArg (fun post : OWNER => post.world.live pointer)
    (PV_THR2_ChildBoundary.effects C {c with store := write c.store ⟨a,i,[]⟩ none}
      site.waiting ⟨.returned (.ok unit),w,events⟩).1

/-- The concrete free primitive ends the selected allocation's lifetime and
keeps every memory byte. The resource answer is an internal branch split, not
a success premise for a whole function. Non-success is handled separately. -/
theorem primitive_success (resources : Resources) (encode : Encode) (w : OWNER)
    (id : Nat) (h : Header) (header : lookup w.world id = some h)
    (answer : (resources (.free h.pointer) (world w)).answer = .returned (.ok ())) :
    let r := PV_EVHB_OwnerHeap.primitive resources encode id (.free h.pointer) w
    r.answer = .returned (.ok ()) ∧ r.world.world.live h.pointer = false ∧
    r.world.world.allocator.metadata h.pointer = none ∧
    r.world.world.memory = w.world.memory ∧ r.world.places = w.places ∧ r.world.next = w.next := by
  simp [PV_EVHB_OwnerHeap.primitive,header,answer,PV_EVHB_OwnerHeap.effect,
    freeAllocation,backend,withWorld]

/-- Failed/pending/faulting/diverging free does not end a source allocation's
OWNER lifetime or silently clear its byte map. Allocator backend/errno may
still advance, as the actual resource reply says. -/
theorem primitive_non_success (resources : Resources) (encode : Encode) (w : OWNER)
    (id : Nat) (h : Header) (header : lookup w.world id = some h)
    (notReturned : ∀ v, (resources (.free h.pointer) (world w)).answer ≠ .returned (.ok v)) :
    let r := PV_EVHB_OwnerHeap.primitive resources encode id (.free h.pointer) w
    r.world.world.live = w.world.live ∧ r.world.world.memory = w.world.memory ∧
    r.world.world.allocator.metadata = w.world.allocator.metadata ∧
    r.world.places = w.places ∧ r.world.next = w.next := by
  simp only [PV_EVHB_OwnerHeap.primitive,header]
  cases hr : (resources (.free h.pointer) (world w)).answer with
  | pending => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | fault f => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | returned result =>
    cases result with
    | fail e => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
    | div => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
    | ok v => exact False.elim (notReturned v hr)

#print axioms old_world_unchanged
#print axioms primitive_success
#print axioms primitive_non_success
end PV_LIB_A_FreeLifetime9
