import PV_LIB_SPEC_LaneA_A_ArcStoreV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ThreadCloneStore
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_THR2_SourceStoreLibrary PV_LIB_A_StorePrimitiveV2

/-- Thread58.field0 is Pin<Arc<Inner>>. Follow the actual source fields,
not a guessed pointer chosen from the native result. N95808/body9110–9116;
std/thread/thread.rs derive Clone; core/pin.rs Clone; alloc/sync.rs Clone.
Thread214's already named operator fact covers its result representation only. -/
def pointer {W : Type} (C : Carrier W Data) (args : List Data)
    (s : Store Data) (w : W) : Option Data := do
  match args with
  | [reference] =>
    let (_,thread) ← receiver C s w reference
    let pin ← C.field thread 0
    let arc ← C.field pin 0
    let nonNull ← C.field arc 0
    C.field nonNull 0
  | _ => none

/-- Exact source-backed Thread::clone214 projection. The Pin/Thread wrappers
add no count action of their own; the one Arc clone increments before its
possible overflow abort. Undefined representations are not called pure.
This function deliberately does not claim OWNER-only pointer coverage. -/
def PV_THR2_LibrarySemantics_ThreadCloneSource214 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) := do
  let ptr ← pointer C args s w
  let p ← C.dereference w ptr
  let count := PV_THR2_LibrarySemantics_ArcClone.countAddress p
  let n ← numberAt C s count
  writeAddress C s count (some (.number ((n+1)%modulus)))

theorem pointer_from_source {W : Type} (C : Carrier W Data) (s : Store Data) (w : W)
    (reference thread pin arc nonNull ptr : Data) (q : Address)
    (received : receiver C s w reference = some (q,thread))
    (threadField : C.field thread 0 = some pin)
    (pinField : C.field pin 0 = some arc)
    (arcField : C.field arc 0 = some nonNull)
    (pointerField : C.field nonNull 0 = some ptr) :
    pointer C [reference] s w = some ptr := by
  unfold pointer
  change (receiver C s w reference).bind _ = _
  rw [received]
  change (C.field thread 0).bind _ = _
  rw [threadField]
  change (C.field pin 0).bind _ = _
  rw [pinField]
  change (C.field arc 0).bind _ = _
  rw [arcField]
  exact pointerField

/-- The wrapper's entire source count action is the SAME named Arc action.
All full replies (and their worlds/events) are retained by the table's delivery;
no successful answer or overflow-free count is needed for this equality. -/
theorem source_count {W : Type} (C : Carrier W Data) (s : Store Data) (w : W)
    (args : List Data) (ptr : Data) (p : Address) (n : Nat)
    (selected : pointer C args s w = some ptr)
    (address : C.dereference w ptr = some p)
    (count : numberAt C s (PV_THR2_LibrarySemantics_ArcClone.countAddress p) = some n) :
    PV_THR2_LibrarySemantics_ThreadCloneSource214 C args s w =
      writeAddress C s (PV_THR2_LibrarySemantics_ArcClone.countAddress p)
        (some (.number ((n+1)%modulus))) := by
  unfold PV_THR2_LibrarySemantics_ThreadCloneSource214
  rw [selected]
  change (C.dereference w ptr).bind _ = _
  rw [address]
  change (numberAt C s (PV_THR2_LibrarySemantics_ArcClone.countAddress p)).bind _ = _
  rw [count]
  rfl

#print axioms pointer
#print axioms PV_THR2_LibrarySemantics_ThreadCloneSource214
#print axioms pointer_from_source
#print axioms source_count
end PV_LIB_A_ThreadCloneStore
