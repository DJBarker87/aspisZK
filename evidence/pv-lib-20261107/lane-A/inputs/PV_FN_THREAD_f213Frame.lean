import PV_FN_THREAD_f361SelectedNative
set_option autoImplicit false
noncomputable section
namespace PV_THR2_LibrarySemantics_ThreadNew213
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_EVHB_RawVecOwner

/-- A semantic view of the OPAQUE String (N95807 type84), not an invented
source field path or a claim about its unspecified native field ordering.
The type interpretation supplies decode; its original-machine adequacy remains
an explicit named representation obligation. No frame or run occurs in it. -/
structure Buffer where
  address : Address
  pointer : Nat
  length : Nat
  capacity : Nat
  bytes : List UInt8

structure Representation where
  decode : Data → Option Buffer

def sourcePlace (p : Address) : PV_EVHB_SourceLifetimes.Place :=
  ⟨p.activation,p.localIndex :: p.fields⟩

/-- Caller-supplied String buffer validity, including the empty/dangling
case via the existing Owned predicate. This is an ownership facet; arbitrary
UTF-8 bytes, including interior NULs, are retained. -/
def Owned (w : OWNER) (b : Buffer) : Prop :=
  ∃ (id : Nat) (header : Header),
    w.places (sourcePlace b.address) = some id ∧
    lookup w.world id = some header ∧
    PV_EVHB_RawVecOwner.Owned w.world header ∧
    header.pointer = b.pointer ∧ header.len = b.length ∧ header.cap = b.capacity ∧
    header.shape.width = 1 ∧ b.pointer ≠ 0 ∧ b.length ≤ b.capacity ∧
    b.pointer + b.capacity ≤ 2^64 ∧ b.capacity < 2^63 ∧ b.bytes.length = b.length ∧
    (∀ i byte, b.bytes[i]? = some byte →
      w.world.memory (b.pointer+i) = some byte.toNat) ∧
    ∃ text : String, text.toUTF8.data.toList = b.bytes

/-- Both source Option constructors, with arbitrary descriptor metadata.
Only the opaque String payload uses the explicit representation interpreter. -/
inductive NameOwned (R : Representation) (w : OWNER) : Data → Option Buffer → Prop where
  | none (descriptor metadata : Data) :
      NameOwned R w (PV_THR2_KeyValues.pack
        (.object [("Adt",.array [descriptor,.number 0,metadata])]) []) none
  | some (descriptor metadata value : Data) (buffer : Buffer)
      (decoded : R.decode value = some buffer) (owned : Owned w buffer) :
      NameOwned R w (PV_THR2_KeyValues.pack
        (.object [("Adt",.array [descriptor,.number 1,metadata])]) [value]) (some buffer)

/-- Projection of the exact old SOURCE buffer root. Fresh heap allocations,
resizing/freeing the owned name, backend effects and events are not erased or
asserted equal. Interior buffer fields share this source root. -/
def InBuffer (view : Option Buffer) (p : Address) : Prop :=
  ∃ b, view = some b ∧ p = {b.address with fields := []}

structure Returned (C : Carrier OWNER Data) (e : PV_W1_LeafBoundary.Entry)
    (w : OWNER) (changes : Address → Option Data) (view : Option Buffer) : Prop where
  cells : ∀ p, ¬ InBuffer view p →
    (PV_W1_ArgumentEffects.finalStore C e w changes).cells p = e.store.cells p

/-! Exact f213 = std::thread::Thread::new(ThreadId, Option<String>).
Pinned bodies and full-file hashes: session19-source/manifest.json, entries
0..7. Thread::new maps the name through ThreadNameString::from, which calls
CString::new(String); _from_vec_unchecked reserves one byte, pushes NUL, then
into_boxed_slice may resize the allocation. The Thread Inner allocation and
Parker initialization act in fresh heap memory. ThreadId is passed by value.
Thus the old source-store footprint is confined to the owned name buffer.
This is ONLY that source-cell projection, not a complete heap/allocator
semantics or a world-identity assertion. The complete arbitrary world/reply
is kept. Original-handler satisfaction and the String interpretation remain
named Recount14 obligations under thread16/thread7, never T fields.
No ownership or representation premise is added to a f361 run here. -/
def Fact {E : Type} (R : Representation) (C : Carrier OWNER Data)
    (e : PV_W1_LeafBoundary.Entry) (H : PV_W1_OwnerNativeFrame.Backend E)
    (w : OWNER) (changes : Address → Option Data) : Prop :=
  PV_THR2_OffPath.functionId e.callee = some 213 →
  ∀ id label view, e.arguments = [id,label] → NameOwned R w label view →
    let r := PV_THR2_OwnUniformResourceHandler.lift H
      (.child e.callee e.store.nextActivation e.arguments) w
    ∀ result, r.answer = .returned (.ok result) → Returned C e w changes view

#print axioms sourcePlace
#print axioms Owned
#print axioms NameOwned
#print axioms InBuffer
#print axioms Returned
#print axioms Fact
end PV_THR2_LibrarySemantics_ThreadNew213

namespace PV_FN_THREAD_f213
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_THR2_LibrarySemantics_ThreadNew213

def PostFrame {E : Type} (C : Carrier OWNER Data) (e : PV_W1_LeafBoundary.Entry)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER) (events : List E)
    (changes : Address → Option Data) (view : Option Buffer) : Prop :=
  PV_W1_ArgumentEffects.Post C e H w events changes ∧
  ∀ result, (PV_THR2_OwnUniformResourceHandler.lift H
    (.child e.callee e.store.nextActivation e.arguments) w).answer = .returned (.ok result) →
    Returned C e w changes view

theorem contract_frame {E : Type} (R : Representation) (C : Carrier OWNER Data)
    (e : PV_W1_LeafBoundary.Entry) (H : PV_W1_OwnerNativeFrame.Backend E)
    (w : OWNER) (events : List E) (changes : Address → Option Data)
    (pre : PV_W1_ClosedLeaves.Pre e w)
    (function : PV_THR2_OffPath.functionId e.callee = some 213)
    (id label : Data) (view : Option Buffer) (arguments : e.arguments = [id,label])
    (owned : NameOwned R w label view) (semantics : Fact R C e H w changes) :
    PostFrame C e H w events changes view :=
  ⟨PV_W1_ArgumentEffects.full_reply C e H w events changes pre,
    semantics function id label view arguments owned⟩

theorem implies_W1 {E : Type} (C : Carrier OWNER Data) (e : PV_W1_LeafBoundary.Entry)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER) (args : List Data)
    (events : List E) (changes : Address → Option Data) (pre : PV_W1_ClosedLeaves.Pre e w)
    (view : Option Buffer)
    (post : PostFrame C (PV_W1_NativeLeaves.entry213 e args) H w events changes view) :
    PV_W1_NativeLeaves.Post213 C e H w args events changes :=
  ⟨post.1,PV_W1_OwnerWellFormed.fresh_callee w e.store.nextActivation pre⟩

theorem returned_cell {E : Type} (C : Carrier OWNER Data) (e : PV_W1_LeafBoundary.Entry)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER) (events : List E)
    (changes : Address → Option Data) (view : Option Buffer)
    (post : PostFrame C e H w events changes view) (result : Data)
    (answer : (PV_THR2_OwnUniformResourceHandler.lift H
      (.child e.callee e.store.nextActivation e.arguments) w).answer = .returned (.ok result))
    (p : Address) (outside : ¬ InBuffer view p) (foreign : p.activation ≠ e.store.nextActivation)
    (notReturn : p ≠ (⟨e.caller,e.destination,[]⟩ : Address)) :
    (PV_W1_LeafBoundary.statusStore (PV_W1_LeafBoundary.deliver C
      (PV_W1_ArgumentEffects.afterEffects C e w changes)
      (PV_THR2_OwnUniformResourceHandler.lift H
        (.child e.callee e.store.nextActivation e.arguments) w) events).current.status).cells p =
      e.store.cells p :=
  (post.1.1.2.2.2.2 p foreign notReturn).trans ((post.2 result answer).cells p outside)

#print axioms PostFrame
#print axioms contract_frame
#print axioms implies_W1
#print axioms returned_cell
end PV_FN_THREAD_f213
