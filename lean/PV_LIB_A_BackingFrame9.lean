import PV_LIB_A_ProviderBacking9
import PV_THR2_OwnUniformResourceHandler
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_BackingFrame9
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_RawVecOwner
open PV_LIB_A_AllocationBacking9

/-- Every lifted native reply frames the registered source backing, including
pending/failure/abort/divergence. No success or no-effect assumption is added. -/
theorem native (H : PV_W1_OwnerNativeFrame.Backend PV_RJ4IDB.NativeEvent)
    (request : PV_STX2_Native.Request Data) (w : OWNER) (p : Address) :
    select (PV_THR2_OwnUniformResourceHandler.lift H request w).world p = select w p := rfl

/-- A later source registration cannot replace an earlier allocation identity.
The id inequality follows from the EXISTING freshness invariant. The source
place inequality follows from activation numbering, not an alias premise. -/
theorem newer_registration (w : OWNER) (p : Address)
    (q : PV_EVHB_OwnerMachine.Place) (shape : R1Z.PV_FXM_ReserveWorld.Shape) (align id : Nat)
    (h : Header) (fresh : PV_EVHB_SourceLifetimes.Fresh w)
    (registered : w.places (place p) = some id) (header : lookup w.world id = some h)
    (older : p.activation < q.activation) :
    select (PV_EVHB_SourceLifetimes.newAt w q shape align) p = some ⟨id,h⟩ := by
  have different : place p ≠ q := by
    intro same
    have bad := congrArg PV_EVHB_SourceLifetimes.Place.activation same
    exact (Nat.ne_of_lt older) bad
  have prior : id ≠ w.next := Nat.ne_of_lt (fresh (place p) id registered)
  apply selected
  · simp only [PV_EVHB_SourceLifetimes.newAt,if_neg different]
    exact registered
  · change lookup (store w.world w.next (PV_EVHB_SourceLifetimes.emptyHeader shape align)) id = _
    rw [lookup_other _ _ _ _ prior]
    exact header

/-- Free retains historical descriptors, but makes the pointed allocation
nonlive. A descriptor surviving is not evidence that its allocation is Owned. -/
theorem free_registry (w : OWNER) (pointer : Nat) (p : Address) :
    select (PV_EVHB_OwnerHeap.freeAllocation w pointer) p = select w p := rfl

#print axioms native
#print axioms newer_registration
#print axioms free_registry
end PV_LIB_A_BackingFrame9
