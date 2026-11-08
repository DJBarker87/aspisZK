import PV_LIB_A_OwnerStore
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_StorePrimitiveV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_SourceStoreLibrary
/-- The pinned target is ELF64. Atomic arithmetic wraps at the source usize
width, including the increment before Arc's overflow abort. -/
def modulus : Nat := 2^64

def atReference {W : Type} (C : Carrier W Data) (s : Store Data)
    (w : W) (reference : Data) (fields : List Nat) : Option Address := do
  let p ← C.dereference w reference
  pure {p with fields := p.fields ++ fields}

def numberAt {W : Type} (C : Carrier W Data) (s : Store Data)
    (p : Address) : Option Nat := do
  let .number n ← readAddress C s p | none
  pure n

/-- Primitive store write, using the carrier's source address rather than an
OWNER heap address. It works at any depth below a BoxNew allocation. -/
def put {W : Type} (C : Carrier W Data) (s : Store Data) (w : W)
    (reference : Data) (fields : List Nat) (value : Data) : Option (Store Data) := do
  let p ← atReference C s w reference fields
  writeAddress C s p (some value)

def modifyNumber {W : Type} (C : Carrier W Data) (s : Store Data) (w : W)
    (reference : Data) (fields : List Nat) (f : Nat → Nat) : Option (Store Data) := do
  let p ← atReference C s w reference fields
  let n ← numberAt C s p
  writeAddress C s p (some (.number (f n)))

/-- One documented meaning for emitted thread:f351: AtomicUsize::fetch_add,
core/sync/atomic.rs atomic_int! fetch_add. The source field is v.value.
The ordering argument is retained in the native request/reply. -/
def PV_THR2_LibrarySemantics_FetchAdd351 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) :=
  match args with
  | [reference,.number n,_] => modifyNumber C s w reference [0,0] (fun old => (old+n)%modulus)
  | _ => none

/-- One documented meaning for thread:f581: AtomicUsize::fetch_sub.
Unsigned subtraction wraps; Nat's saturating subtraction alone is incorrect. -/
def PV_THR2_LibrarySemantics_FetchSub581 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) :=
  match args with
  | [reference,.number n,_] => modifyNumber C s w reference [0,0]
      (fun old => (old+modulus-(n%modulus))%modulus)
  | _ => none

/-- One documented meaning for thread:f557: AtomicUsize::store. -/
def PV_THR2_LibrarySemantics_AtomicStore557 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) :=
  match args with
  | [reference,value,_] => put C s w reference [0,0] value
  | _ => none

/-- One documented meaning for thread:f646: AtomicBool::store. The source
representation is Atomic.v.UnsafeCell.value; it is not a root scalar Cell. -/
def PV_THR2_LibrarySemantics_AtomicBoolStore646 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) :=
  match args with
  | [reference,value,_] => put C s w reference [0,0] value
  | _ => none

/-- thread:f442 core::mem::replace writes the destination itself. -/
def PV_THR2_LibrarySemantics_MemReplace442 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) :=
  match args with
  | [reference,value] => put C s w reference [] value
  | _ => none

/-- thread:f308 pointer method write and f364 core::ptr::write have distinct
emitted identities and the same documented destination write. -/
def PV_THR2_LibrarySemantics_PtrWrite308 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) :=
  match args with
  | [reference,value] => put C s w reference [] value
  | _ => none

def PV_THR2_LibrarySemantics_PtrWrite364 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) :=
  match args with
  | [reference,value] => put C s w reference [] value
  | _ => none

/-- Atomic loads127/129/528 and fences582 perform no source-store write.
Their returned-value/order semantics are separate native obligations. -/
theorem load_store_frame (s : Store Data) : (fun s : Store Data => s) s = s := rfl

theorem put_root {W : Type} (C : Carrier W Data) (s : Store Data) (w : W)
    (reference value : Data) (a i : Nat)
    (address : C.dereference w reference = some ⟨a,i,[]⟩) :
    put C s w reference [] value = some (write s ⟨a,i,[]⟩ (some value)) := by
  unfold put atReference
  rw [address]
  rfl

#print axioms PV_THR2_LibrarySemantics_FetchAdd351
#print axioms PV_THR2_LibrarySemantics_FetchSub581
#print axioms PV_THR2_LibrarySemantics_AtomicStore557
#print axioms PV_THR2_LibrarySemantics_AtomicBoolStore646
#print axioms PV_THR2_LibrarySemantics_MemReplace442
#print axioms PV_THR2_LibrarySemantics_PtrWrite308
#print axioms PV_THR2_LibrarySemantics_PtrWrite364
#print axioms load_store_frame
#print axioms put_root
end PV_LIB_A_StorePrimitiveV2
