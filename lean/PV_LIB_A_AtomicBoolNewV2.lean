import PV_LIB_A_AtomicReadsV2
import PV_W1_ClosedLeaves
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_AtomicBoolNewV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
/-- The pinned source constructs UnsafeCell<u8> with v as u8. The emitted
atomic/UnsafeCell tags are representation metadata; the held byte is exact. -/
def Holds (value : Data) (b : Bool) : Prop :=
  ∃ atomicKind unsafeKind, value = PV_THR2_KeyValues.pack atomicKind
    [PV_THR2_KeyValues.pack unsafeKind [.number (if b then 1 else 0)]]

/-- ONE named documented fact for opaque123, core/sync/atomic.rs
AtomicBool::new. This is a lower source-semantics obligation, not an axiom,
T field or an assertion that every arbitrary backend obeys it. -/
def PV_THR2_LibrarySemantics_AtomicBoolNew123 {E : Type}
    (e : Entry) (H : Backend E) (w : OWNER) (b : Bool) : Prop :=
  let d := PV_W1_NamedLeafBoundary.entry e (PV_W1_NamedLeafBoundary.function PV_THR2_F6.node20) [.boolean b]
  ∀ value, (PV_LIB_A_AtomicReadsV2.actual H d w).answer = .returned (.ok value) →
    Holds value b ∧ (PV_LIB_A_AtomicReadsV2.actual H d w).world = w

theorem held_byte (C : Carrier OWNER Data) (branch b : Bool) (value : Data)
    (held : Holds value b) :
    readFields (PV_THR2_OwnInitExactReturnedCases.carrier C branch) [0,0] value =
      some (.number (if b then 1 else 0)) := by
  rcases held with ⟨ak,uk,rfl⟩
  rfl

/-- Instantiate the actual CLOSED leaf, then expose its stronger byte value.
Every nonreturned answer remains in the original provider Post. -/
theorem certified {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E)
    (w : OWNER) (es : List E) (b : Bool)
    (pre : PV_W1_ClosedLeaves.Pre e w)
    (fact : PV_THR2_LibrarySemantics_AtomicBoolNew123 e H w b) :
    PV_W1_ClosedLeaves.Post123 C e H w [.boolean b] es ∧
      ∀ value, (PV_LIB_A_AtomicReadsV2.actual H (PV_W1_NamedLeafBoundary.entry e (PV_W1_NamedLeafBoundary.function PV_THR2_F6.node20) [.boolean b]) w).answer =
        .returned (.ok value) → Holds value b := by
  exact ⟨PV_W1_ClosedLeaves.f123 C e H w [.boolean b] es pre,
    fun value answer => (fact value answer).1⟩

#print axioms PV_THR2_LibrarySemantics_AtomicBoolNew123
#print axioms held_byte
#print axioms certified
end PV_LIB_A_AtomicBoolNewV2
