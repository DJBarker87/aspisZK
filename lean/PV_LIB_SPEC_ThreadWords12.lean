import PV_LIB_SPEC_SourceNative12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ThreadWords12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_Frozen PV_LIB_SPEC_D984
open PV_LIB_SPEC_AllocationImages
abbrev Pointer := PV_OWN2_Codec.Pointer
/-- ELF64 qword read from the actual physical snapshot; unknown bytes stay
unknown. The existing bounded codec never truncates an unbounded numeral. -/
def read (w : OWNER) (address : Nat) : Option Pointer :=
  PV_OWN2_Codec.decodePointer (fun i => w.world.memory (address+i.val))
def wordImage (value : Nat) : Image := fun i => if i<8 then word value i else none
def write (w : OWNER) (address value : Nat) : OWNER := initialized address (wordImage value) w

theorem read_written (w : OWNER) (address : Nat) (value : Pointer) :
    read (write w address value.val) address = some value := by
  have bytes : (fun i : Fin 8 => (write w address value.val).world.memory (address+i.val)) =
      (fun i => some (PV_OWN2_WordImage.pointerBytes value i).val) := by
    funext i
    apply stored
    exact if_pos i.isLt
  unfold read
  rw [bytes,PV_OWN2_Codec.decode_pointer_image,PV_OWN2_WordImage.pointerBytes_value]

def increment (base : Nat) (value : Data) (w : OWNER)
    (r : Reply OWNER Event Data) : Option (Reply OWNER Event Data) := do
  let count ← read w base
  let next := (count.val+1) % 2^64
  let changed := write r.world base next
  /- Adopted current_or_unnamed17c4a1 and its JLE17c4a6 test the incremented
     signed count. This flag test is stated literally, not inferred from an
     unproved absence of overflow in a source count. -/
  if next=0 ∨ 2^63 ≤ next then pure ⟨.fault .abort,changed,r.events⟩
  else pure ⟨.returned (.ok value),changed,r.events⟩

/-- Initialized-TLS branch only: TLS contains the pointer to Inner,16 bytes
past ArcInner.17c498 reads it;17c4a1 increments at-16;17c4ac returns ArcInner.
The ≤2 uninitialized/destroyed cases explicitly remain interpretation gaps;
they are not replaced by a successful constructor or a no-allocation claim. -/
def current (tlsSlot : Nat) (w : OWNER) (r : Reply OWNER Event Data) :
    Option (Reply OWNER Event Data) :=
  match r.answer with
  | .returned (.ok _) => do
    let inner ← read w tlsSlot
    if inner.val≤16 then none else
      increment (inner.val-16) (.number (inner.val-16)) w r
  | _ => some r

/-- Thread::clone receives &Thread. Its numeric physical ArcInner comes from
the actual source store, then the physical count is read before the native
increment. Value-only OperatorCloneHandler remains the delivery adapter. -/
def clone (p : Parameters) (c : Config) (w : OWNER) (args : List Data)
    (r : Reply OWNER Event Data) : Option (Reply OWNER Event Data) :=
  match r.answer with
  | .returned (.ok _) => do
    let [reference] := args | none
    let address ← (runtime p).carrier.dereference w reference
    let value ← readAddress (runtime p).carrier c.store address
    let pointer ← PV_THR2_OwnInitPointerCodec.decode value
    increment pointer.val value w r
  | _ => some r

/-- All nonreturned-success arms preserve the complete native reply, including
pending/failure/divergence/fault and every side event. -/
theorem current_other (slot : Nat) (w : OWNER) (r : Reply OWNER Event Data)
    (other : ∀ v, r.answer ≠ .returned (.ok v)) : current slot w r = some r := by
  cases h : r.answer with
  | pending => simp only [current,h]
  | fault f => simp only [current,h]
  | returned result => cases result with
    | ok v => exact False.elim (other v h)
    | fail e => simp only [current,h]
    | div => simp only [current,h]

/-- The physical write never mutates OWNER ghost descriptors. -/
theorem ghost_write (w : OWNER) (base value : Nat) :
    PV_LIB_SPEC_NativeRuntime.GhostFrame w (write w base value) := ghost _ _ _

#print axioms read
#print axioms wordImage
#print axioms write
#print axioms read_written
#print axioms increment
#print axioms current
#print axioms clone
#print axioms current_other
#print axioms ghost_write
end PV_LIB_SPEC_ThreadWords12
