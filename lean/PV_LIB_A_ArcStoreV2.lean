import PV_LIB_A_StorePrimitiveV2
import PV_THR2_LibrarySemantics_ArcClone
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ArcStoreV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_SourceStoreLibrary PV_LIB_A_StorePrimitiveV2
/-- Follow the actual Arc.ptr.NonNull.pointer chain into the source store.
The pointer may name a BoxNew allocation in a different activation. -/
def inner {W : Type} (C : Carrier W Data) (args : List Data)
    (s : Store Data) (w : W) : Option Address := do
  match args with
  | [reference] =>
    let (_,arc) ← receiver C s w reference
    let nonNull ← C.field arc 0
    let pointer ← C.field nonNull 0
    C.dereference w pointer
  | _ => none

/-- D984: ONE named documented meaning for emitted thread:f360.
Rust alloc/sync.rs Clone for Arc: strong.fetch_add(1,Relaxed), THEN the
MAX_REFCOUNT abort check. Even the abort prefix contains the increment.
Only the source-store projection is defined here; the full backend reply,
including overflow abort, pending and failure, is never replaced. -/
def PV_THR2_LibrarySemantics_ArcClone360 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) := do
  let p ← inner C args s w
  let count := PV_THR2_LibrarySemantics_ArcClone.countAddress p
  let n ← numberAt C s count
  writeAddress C s count (some (.number ((n+1)%modulus)))

/-- The address is derived from source reads and the typed pointer, not a
chosen write footprint or Store transformer. -/
theorem inner_from_source {W : Type} (C : Carrier W Data) (s : Store Data) (w : W)
    (reference : Data) (arcAddress p : Address) (arc nonNull pointer : Data)
    (ref : C.dereference w reference = some arcAddress)
    (cell : readAddress C s arcAddress = some arc)
    (field : C.field arc 0 = some nonNull)
    (ptr : C.field nonNull 0 = some pointer)
    (deref : C.dereference w pointer = some p) :
    inner C [reference] s w = some p := by
  have received : receiver C s w reference = some (arcAddress,arc) := by
    unfold receiver
    rw [ref]
    change (readAddress C s arcAddress).bind _ = _
    rw [cell]
    rfl
  unfold inner
  change (receiver C s w reference).bind _ = _
  rw [received]
  change (C.field arc 0).bind _ = _
  rw [field]
  change (C.field nonNull 0).bind _ = _
  rw [ptr]
  exact deref

/-- Symbolic count law, retaining machine-width wrapping. -/
theorem clone_count {W : Type} (C : Carrier W Data) (s : Store Data) (w : W)
    (args : List Data) (p : Address) (n : Nat)
    (resolved : inner C args s w = some p)
    (count : readAddress C s (PV_THR2_LibrarySemantics_ArcClone.countAddress p) = some (.number n)) :
    PV_THR2_LibrarySemantics_ArcClone360 C args s w =
      writeAddress C s (PV_THR2_LibrarySemantics_ArcClone.countAddress p)
        (some (.number ((n+1)%modulus))) := by
  unfold PV_THR2_LibrarySemantics_ArcClone360
  rw [resolved]
  change (numberAt C s (PV_THR2_LibrarySemantics_ArcClone.countAddress p)).bind _ = _
  unfold numberAt
  rw [count]
  rfl

/-- Concrete source wrapper fields are recognized by the existing exact carrier.
This closes no original-entry/history or native returned-value obligation. -/
theorem valid_inner (C : Carrier PV_EVHB_OwnerMachine.OWNER Data) (b : Bool)
    (e : PV_W1_LeafBoundary.Entry) (w : PV_EVHB_OwnerMachine.OWNER)
    (v : PV_THR2_LibrarySemantics_ArcClone.Valid
      (PV_THR2_OwnInitExactReturnedCases.carrier C b) e w) :
    inner (PV_THR2_OwnInitExactReturnedCases.carrier C b) e.arguments e.store w = some v.inner := by
  rw [v.arguments]
  apply inner_from_source _ _ _ _ v.arc v.inner
    (PV_THR2_Packet315SourceReturn.value v.nonNull v.allocator) v.nonNull
    (PV_STX2_TypedReferences.reference v.inner .null)
  · change (PV_STX2_TypedReferences.carrier _).dereference w _ = _
    exact PV_STX2_TypedReferences.dereference _ _ _ _
  · exact v.arcRoot
  · rfl
  · exact v.innerPointer
  · change (PV_STX2_TypedReferences.carrier _).dereference w _ = _
    exact PV_STX2_TypedReferences.dereference _ _ _ _

#print axioms PV_THR2_LibrarySemantics_ArcClone360
#print axioms inner_from_source
#print axioms clone_count
#print axioms valid_inner
end PV_LIB_A_ArcStoreV2
