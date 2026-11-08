import PV_LIB_A_AllocationBacking9
import PV_W1_BoxLeaf
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ProviderBacking9
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner
open PV_W1_LeafBoundary R1Z.PV_FXM_ReserveWorld

/-- The producer's source-minted ARG1 allocation root is exactly the place
used by last-reference lookup. It is not a guessed raw pointer or dead temp. -/
theorem same_place (s : Store Data) :
    PV_LIB_A_AllocationBacking9.place (PV_THR2_PacketBoxBacking.root s) =
      PV_THR2_PacketBoxRegister.place s := rfl

/-- Select the actual producer's registered identity and installed pointer.
Only the allocator's returned branch is projected here; the provider retains
all other answers. No byte-initialization theorem is consumed or re-credited. -/
theorem successful_backing (resources : Resources) (encode : Encode) (e : Entry)
    (w : OWNER) (shape : Shape) (align pointer : Nat)
    (answer : (resources (.malloc shape.width) (world w)).answer = .returned (.ok pointer))
    (nonnull : pointer ≠ 0) :
    PV_LIB_A_AllocationBacking9.select
      (PV_W1_BoxLeaf.call resources encode e w shape align).world
      (PV_THR2_PacketBoxBacking.root e.store) =
        some ⟨w.next,capacityStore
          (pointerStore (PV_EVHB_SourceLifetimes.emptyHeader shape align) pointer) 1⟩ := by
  let r := PV_THR2_PacketBoxResource.reply resources encode e.store w shape align
  let h := PV_EVHB_SourceLifetimes.emptyHeader shape align
  have native : r.answer = .returned (.ok pointer) :=
    (PV_THR2_PacketBoxResource.answer resources encode e.store w shape align).trans answer
  have done := PV_THR2_PacketBoxReply.returned e.store w.next pointer h r native nonnull
  change PV_LIB_A_AllocationBacking9.select
    (PV_THR2_PacketBoxReply.finish e.store w.next h r).world _ = _
  rw [done]
  apply PV_LIB_A_AllocationBacking9.selected
  · change r.world.places (PV_THR2_PacketBoxRegister.place e.store) = some w.next
    rw [(PV_W1_BoxLeaf.resource_frame resources encode e w shape align).1]
    simp only [PV_THR2_PacketBoxRegister.pre,PV_EVHB_SourceLifetimes.newAt,↓reduceIte]
  · exact install_lookup r.world.world w.next h pointer 1

/-- The deallocator therefore uses the SAME physical pointer the actual
BoxNew resource returned, never a numeric encoding of a source activation. -/
theorem matching_free (resources : Resources) (encode : Encode) (e : Entry)
    (w : OWNER) (shape : Shape) (align pointer : Nat)
    (answer : (resources (.malloc shape.width) (world w)).answer = .returned (.ok pointer))
    (nonnull : pointer ≠ 0) :
    let after := (PV_W1_BoxLeaf.call resources encode e w shape align).world
    PV_LIB_A_AllocationBacking9.deallocate resources encode after
      (PV_THR2_PacketBoxBacking.root e.store) =
      some (PV_EVHB_OwnerHeap.primitive resources encode w.next (.free pointer) after) := by
  intro after
  have selected := successful_backing resources encode e w shape align pointer answer nonnull
  have free := PV_LIB_A_AllocationBacking9.exact_primitive resources encode after
    (PV_THR2_PacketBoxBacking.root e.store) _ selected
  exact free

#print axioms same_place
#print axioms successful_backing
#print axioms matching_free
end PV_LIB_A_ProviderBacking9
