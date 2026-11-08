import PV_FN_THREAD_f360Outcomes
set_option autoImplicit false
noncomputable section
namespace PV_THR2_LibrarySemantics_AtomicUsizeNew
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
/-! thread-19 / Recount14. ONE documented-semantics fact, no axiom or T field.
https://doc.rust-lang.org/std/sync/atomic/struct.AtomicUsize.html#method.new
Pinned Rust 1.94.1 e408947bfd200af42db322daf0fadfe7e26d3bd1,
library/core/src/sync/atomic.rs:2703-2705, macro instance:3946-3963.
Full source sha256 66a878ab38a69f39375cf52e0f4f2c62a03fe487b4baa6ebecf3e30f87d904b2.
`pub const fn new(v: $int_type) -> Self { Self {v: UnsafeCell::new(v)} }`.
The two representation kinds remain existential metadata; the held value is
EXACTLY the input, never an arbitrary counter payload. Compiler preservation
and source/extractor association remain their existing named obligations. -/
def entry (e : PV_W1_LeafBoundary.Entry) (n : Nat) :=
  PV_W1_NamedLeafBoundary.entry e
    (PV_W1_NamedLeafBoundary.function PV_THR2_F6.node16) [.number n]

def Holds (result : Data) (n : Nat) : Prop :=
  ∃ atomicKind unsafeCellKind, result =
    PV_FN_THREAD_f360Outcomes.atomicValue atomicKind unsafeCellKind n

structure Returned {E : Type} (C : Carrier OWNER Data)
    (e : PV_W1_LeafBoundary.Entry) (w : OWNER)
    (r : Reply OWNER E Data) (changes : Address → Option Data)
    (result : Data) (n : Nat) : Prop where
  value : Holds result n
  memory : PV_W1_ArgumentEffects.finalStore C e w changes = e.store
  world : r.world = w

/-- Only successful replies are constrained. Failure, fault (including abort),
divergence and pending are the original complete replies, with their effects. -/
def Fact {E : Type} (C : Carrier OWNER Data) (e : PV_W1_LeafBoundary.Entry)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER)
    (changes : Address → Option Data) (n : Nat) : Prop :=
  let d := entry e n
  let r := PV_THR2_OwnUniformResourceHandler.lift H
    (.child d.callee d.store.nextActivation d.arguments) w
  ∀ result, r.answer = .returned (.ok result) → Returned C d w r changes result n

/-- Decode the numeric field using the installed aggregate interpretation. -/
theorem held_value (C : Carrier OWNER Data) (b : Bool) (result : Data) (n : Nat)
    (held : Holds result n) :
    readFields (PV_THR2_OwnInitExactReturnedCases.carrier C b) [0,0] result =
      some (.number n) := by
  rcases held with ⟨atomicKind,unsafeCellKind,rfl⟩
  rfl
#print axioms held_value
end PV_THR2_LibrarySemantics_AtomicUsizeNew
