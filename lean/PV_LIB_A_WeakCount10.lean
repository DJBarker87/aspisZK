import PV_LIB_A_WeakGuardBuildRun10
import PV_LIB_A_FetchSubSource10
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakCount10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_A_StorePrimitiveV2

/-- Use the provider's exact ArcInner aggregate kind and atomic-value
representation. The payload is arbitrary, including a partially dropped value. -/
def inner (strong payload atomicKind unsafeKind : Data) (weak : Nat) : Data :=
  PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
    [strong,PV_FN_THREAD_f360Outcomes.atomicValue atomicKind unsafeKind weak,payload]

/-- Derive the weak count READ from that source root; no count-read condition
is added to a row or to the native683 interface. -/
theorem read_count (C : Carrier OWNER Data) (b : Bool) (s : Store Data)
    (a i n : Nat) (strong payload atomicKind unsafeKind : Data)
    (source : s.cells ⟨a,i,[]⟩ = some (inner strong payload atomicKind unsafeKind n)) :
    numberAt (PV_LIB_A_DestructorValues10.carrier C b) s ⟨a,i,[1,0,0]⟩ = some n := by
  unfold numberAt readAddress
  rw [source]
  rfl

/-- Source write-definedness is DERIVED for the concrete three-field ArcInner
and the provider's AtomicUsize/UnsafeCell wrappers. It preserves every sibling
and every aggregate tag; no final Store transformer is supplied. -/
theorem write_count (C : Carrier OWNER Data) (b : Bool) (s : Store Data)
    (a i n replacement : Nat) (strong payload atomicKind unsafeKind : Data)
    (source : s.cells ⟨a,i,[]⟩ = some (inner strong payload atomicKind unsafeKind n)) :
    writeAddress (PV_LIB_A_DestructorValues10.carrier C b) s ⟨a,i,[1,0,0]⟩
      (some (.number replacement)) =
      some (write s ⟨a,i,[]⟩ (some (inner strong payload atomicKind unsafeKind replacement))) := by
  change (s.cells ⟨a,i,[]⟩).bind _ = _
  rw [source]
  rfl

/-- Both Weak counter branches, with the actual typed source pointer. Count
zero/underflow and all other machine-width values remain explicit, not excluded
by a new count premise. Allocator/free delivery is the following resource step. -/
theorem allocated (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (w : OWNER)
    (a i n : Nat) (strong payload atomicKind unsafeKind : Data)
    (source : s.cells ⟨a,i,[]⟩ = some (inner strong payload atomicKind unsafeKind n)) :
    PV_LIB_A_WeakDropSource.PV_THR2_LibrarySemantics_WeakDropBegin683.allocated
      (PV_LIB_A_DestructorValues10.carrier C b) s w
      (PV_STX2_TypedReferences.reference ⟨a,i,[]⟩ .null) =
      some ⟨write s ⟨a,i,[]⟩ (some (inner strong payload atomicKind unsafeKind
        ((n+modulus-1)%modulus))),
        if n = 1 then .deallocate ⟨a,i,[]⟩ else .done⟩ := by
  unfold PV_LIB_A_WeakDropSource.PV_THR2_LibrarySemantics_WeakDropBegin683.allocated
  have address : (PV_LIB_A_DestructorValues10.carrier C b).dereference w
      (PV_STX2_TypedReferences.reference ⟨a,i,[]⟩ .null) = some ⟨a,i,[]⟩ :=
    PV_LIB_A_DestructorValues10.reference C b _ _ w
  rw [address]
  change (numberAt (PV_LIB_A_DestructorValues10.carrier C b) s ⟨a,i,[1,0,0]⟩).bind _ = _
  rw [read_count C b s a i n strong payload atomicKind unsafeKind source]
  change (writeAddress (PV_LIB_A_DestructorValues10.carrier C b) s ⟨a,i,[1,0,0]⟩
    (some (.number ((n+modulus-1)%modulus)))).bind _ = _
  rw [write_count C b s a i n _ strong payload atomicKind unsafeKind source]
  rfl

#print axioms inner
#print axioms read_count
#print axioms write_count
#print axioms allocated
end PV_LIB_A_WeakCount10
