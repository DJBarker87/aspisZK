import PV_FN_THREAD_f361MetadataEffects
import PV_THR2_Packet315SourceReturn
set_option autoImplicit false
noncomputable section
namespace PV_THR2_LibrarySemantics_ArcClone
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
/-! thread-16 / Recount14 documented-semantics fact, NOT an axiom or T field.
Rust docs: https://doc.rust-lang.org/std/sync/struct.Arc.html#cloning-references
Pinned deployed source: rustc e408947bfd200af42db322daf0fadfe7e26d3bd1,
library/alloc/src/sync.rs:2360-2411, sha256
ce15d00d92133cf1f55cd1905d7fe6b4e23e62090dabff6c68fae2d7fe78fe8f.
Arc<T,Global>::clone calls strong.fetch_add(1, Relaxed), then aborts when
old_size > isize::MAX, then from_inner_in(self.ptr,self.alloc.clone()).
The emitted Arc has ptr, PhantomData, Global fields. The source-store count
path is ArcInner.strong.AtomicUsize.v.UnsafeCell.value. Reference counts are
source memory effects, never replaced by an identity delta. Native events
and all nonsuccess replies remain the actual reply. Compiler preservation
and extractor/deployed-std correspondence retain their existing obligations. -/

def maxRefcount : Nat := 2^63-1

def countAddress (inner : Address) : Address :=
  {inner with fields := inner.fields ++ [0,0,0]}

/-- A live, initialized Arc at this call entry. The numeric law is a genuine
precondition: a type-shaped ArcInner with arbitrary strong payload is weaker. -/
structure Valid (C : Carrier OWNER Data) (e : PV_W1_LeafBoundary.Entry) (w : OWNER) where
  arc : Address
  inner : Address
  nonNull : Data
  allocator : Data
  count : Nat
  function : PV_THR2_OffPath.functionId e.callee = some 360
  arguments : e.arguments = [PV_STX2_TypedReferences.reference arc .null]
  arcRoot : readAddress C e.store arc =
    some (PV_THR2_Packet315SourceReturn.value nonNull allocator)
  innerPointer : C.field nonNull 0 =
    some (PV_STX2_TypedReferences.reference inner .null)
  initialized : ∃ strong weak packet, readAddress C e.store inner =
    some (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1 [strong,weak,packet])
  strongCount : readAddress C e.store (countAddress inner) = some (.number count)
  nonzero : 0 < count
  fits : count < 2^64

/-- All reads except the atomic strong-count subobject are unchanged. Keeping
this at source addresses also frames Packet and weak-count fields. -/
def OutsideCount (inner p : Address) : Prop :=
  p.activation ≠ inner.activation ∨ p.localIndex ≠ inner.localIndex ∨
    ¬ (p.fields.IsPrefix (countAddress inner).fields ∨
       (countAddress inner).fields.IsPrefix p.fields)

structure Returned {E : Type} (C : Carrier OWNER Data)
    (e : PV_W1_LeafBoundary.Entry) (w : OWNER) (v : Valid C e w)
    (r : Reply OWNER E Data) (changes : Address → Option Data) (result : Data) : Prop where
  value : result = PV_THR2_Packet315SourceReturn.value v.nonNull v.allocator
  bounded : v.count ≤ maxRefcount
  increment : readAddress C (PV_W1_ArgumentEffects.finalStore C e w changes)
    (countAddress v.inner) = some (.number (v.count+1))
  arcCells : (PV_W1_ArgumentEffects.finalStore C e w changes).cells
    {v.arc with fields := []} = e.store.cells {v.arc with fields := []}
  readFrame : ∀ p, OutsideCount v.inner p →
    readAddress C (PV_W1_ArgumentEffects.finalStore C e w changes) p = readAddress C e.store p
  cellFrame : ∀ p, p ≠ {v.inner with fields := []} →
    (PV_W1_ArgumentEffects.finalStore C e w changes).cells p = e.store.cells p
  /-- Atomic bookkeeping lives in the explicit source-store delta. The backend
  component has no allocator/OS request for this Global specialization. -/
  world : r.world = w

/-- ONE named fact at the actual call entry for the emitted library boundary.
The backend handler may close over this entry store; it is not required to
return one fixed Arc across incompatible source stores. Returned
successes obey the source footprint; all other answers retain their complete
reply and explicit store. In particular success beyond MAX_REFCOUNT is not
admitted; the source abort terminal remains represented by Fault.abort. -/
def Fact {E : Type} (C : Carrier OWNER Data) (e : PV_W1_LeafBoundary.Entry)
    (H : PV_W1_OwnerNativeFrame.Backend E) (w : OWNER)
    (changes : Address → Option Data) : Prop :=
  ∀ v : Valid C e w,
    let r := PV_THR2_OwnUniformResourceHandler.lift H
      (.child e.callee e.store.nextActivation e.arguments) w
    ∀ result, r.answer = .returned (.ok result) → Returned C e w v r changes result

/-- The fact excludes a successful return in the overflow branch. It does not
exclude abort, fault, Result failure, divergence, or pending answers. -/
theorem overflow {E : Type} (C : Carrier OWNER Data)
    (H : PV_W1_OwnerNativeFrame.Backend E)
    (effects : PV_W1_LeafBoundary.Entry → OWNER → Address → Option Data)
    (e : PV_W1_LeafBoundary.Entry) (w : OWNER)
    (fact : Fact C e H w (effects e w))
    (v : Valid C e w) (tooLarge : maxRefcount < v.count) (result : Data) :
    (PV_THR2_OwnUniformResourceHandler.lift H
      (.child e.callee e.store.nextActivation e.arguments) w).answer ≠ .returned (.ok result) := by
  intro answer
  exact (Nat.not_le_of_gt tooLarge) (fact v result answer).bounded
#print axioms overflow
end PV_THR2_LibrarySemantics_ArcClone
