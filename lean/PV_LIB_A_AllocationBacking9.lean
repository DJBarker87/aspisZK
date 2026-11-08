import PV_LIB_A_StoreActionTable9
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_AllocationBacking9
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap

/-- A source address selects its OWN registered place. No address is guessed
from matching payload values or a consumer-supplied allocation identity. -/
def place (p : Address) : PV_EVHB_OwnerMachine.Place :=
  ⟨p.activation,p.localIndex :: p.fields⟩

structure Backing where
  identity : Nat
  header : PV_EVHB_RawVecOwner.Header

def select (w : OWNER) (p : Address) : Option Backing :=
  (PV_EVHB_OwnerMachine.receiver w (place p)).map (fun (id,h) => ⟨id,h⟩)

/-- Use the existing allocator primitive and its explicit resource channel.
Missing backing is an interpretation gap, never a guessed Global free. -/
def deallocate (resources : Resources) (encode : Encode) (w : OWNER) (p : Address) :
    Option (Reply OWNER PV_RJ4IDB.NativeEvent Unit) := do
  let b ← select w p
  pure (PV_EVHB_OwnerHeap.primitive resources encode b.identity (.free b.header.pointer) w)

/-- The source/OWNER lookup is DERIVED from the source address. -/
theorem selected (w : OWNER) (p : Address) (id : Nat) (h : PV_EVHB_RawVecOwner.Header)
    (registered : w.places (place p) = some id)
    (header : PV_EVHB_RawVecOwner.lookup w.world id = some h) :
    select w p = some ⟨id,h⟩ := by
  simp only [select,PV_EVHB_OwnerMachine.receiver,registered,Option.bind_some,
    header,Option.map_some]

theorem exact_primitive (resources : Resources) (encode : Encode) (w : OWNER)
    (p : Address) (b : Backing) (bound : select w p = some b) :
    deallocate resources encode w p = some
      (PV_EVHB_OwnerHeap.primitive resources encode b.identity (.free b.header.pointer) w) := by
  unfold deallocate
  rw [bound]
  rfl

/-- Free ends the allocation lifetime, while preserving every byte's previous
content, including stale bytes. It does NOT create or zero a byte image. -/
theorem free_lifetime (w : OWNER) (pointer : Nat) :
    (freeAllocation w pointer).world.live pointer = false ∧
    (freeAllocation w pointer).world.allocator.metadata pointer = none ∧
    (freeAllocation w pointer).world.memory = w.world.memory ∧
    (freeAllocation w pointer).places = w.places ∧
    (freeAllocation w pointer).next = w.next := by
  simp [freeAllocation,withWorld]

/-- Registered identities remain historical descriptors after free, but no
Owned claim survives a nonempty allocation's ended lifetime. -/
theorem no_owned_after_free (w : OWNER) (h : PV_EVHB_RawVecOwner.Header) (cap : h.cap ≠ 0) :
    ¬ PV_EVHB_RawVecOwner.Owned (freeAllocation w h.pointer).world h :=
  PV_EVHB_OwnerHeap.free_consumes w h cap

/-- A registered source root is necessary. Erased pointer or type metadata
alone never manufactures a backing; unknown source allocations stay missing. -/
theorem unregistered (w : OWNER) (p : Address) (missing : w.places (place p) = none) :
    select w p = none := by
  simp only [select,PV_EVHB_OwnerMachine.receiver,missing,Option.bind_none,Option.map_none]

#print axioms place
#print axioms select
#print axioms deallocate
#print axioms selected
#print axioms exact_primitive
#print axioms free_lifetime
#print axioms no_owned_after_free
#print axioms unregistered
end PV_LIB_A_AllocationBacking9
