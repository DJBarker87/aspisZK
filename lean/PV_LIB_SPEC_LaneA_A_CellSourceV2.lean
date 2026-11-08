import PV_LIB_A_CellTakeV2
import PV_LIB_A_AtomicReadsV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_CellSourceV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_THR2_SourceStoreLibrary PV_LIB_A_StorePrimitiveV2
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
/-- Cell is opaque type26 in the emission and repr(transparent) in Rust.
Use the SAME transparent payload view already adopted for Cell::replace289.
This works through references into boxes too. Cell::set's subsequent old-value
destructor is NOT supplied by this direct-write PREFIX; its composition is open. -/
def PV_THR2_LibrarySemantics_CellSetPrefix504 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) :=
  match args with
  | [reference,value] => put C s w reference [] value
  | _ => none

/-- Complete source-store projection ONLY for Cell<bool>::set. Dropping the
old bool has no destructor; arbitrary T (including SpawnHooks) is deliberately
unsupported. The type-specific caller binding remains a lower obligation. -/
def PV_THR2_LibrarySemantics_CellBoolSet504 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) :=
  match args with
  | [reference,.boolean b] => put C s w reference [] (.boolean b)
  | _ => none

/-- Exact641 specialization T=SpawnHooks: Default constructs first=None, then
mem::take returns the old value without dropping it. Both the opaque Cell and
its UnsafeCell use the adopted transparent payload view, as289 does. -/
def PV_THR2_LibrarySemantics_CellTake641 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) := do
  match args with
  | [reference] =>
    let (p,old) ← receiver C s w reference
    let empty ← PV_LIB_A_CellTakeV2.defaultSpawnHooks old
    writeAddress C s p (some empty)
  | _ => none

/-- Named source representation fact for Cell::new371 (not UnsafeCell::new455).
It binds the opaque Cell's source value to its transparent T payload. Its
actual native/backend instance remains a lower obligation, not an axiom/T item. -/
def PV_THR2_LibrarySemantics_CellNew371 {E : Type}
    (e : Entry) (H : Backend E) (w : OWNER) : Prop :=
  PV_THR2_OffPath.functionId e.callee = some 371 →
  ∀ input result, e.arguments = [input] →
    (PV_LIB_A_AtomicReadsV2.actual H e w).answer = .returned (.ok result) → result = input

/-- In the adopted scalar-bool view the source write is the same as289's
already documented write, not an attempt to access nonexistent wrapper fields. -/
theorem scalar_set {W : Type} (C : Carrier W Data) (s : Store Data) (w : W)
    (reference : Data) (a i : Nat) (b : Bool)
    (address : C.dereference w reference = some ⟨a,i,[]⟩) :
    PV_THR2_LibrarySemantics_CellSetPrefix504 C [reference,.boolean b] s w =
      some (write s ⟨a,i,[]⟩ (some (.boolean b))) :=
  put_root C s w reference (.boolean b) a i address

/-- Construct the exact empty source SpawnHooks value from the current source
metadata. No default-value or desired Store transformer is supplied by a caller. -/
theorem take_root {W : Type} (C : Carrier W Data) (s : Store Data) (w : W)
    (reference : Data) (a i : Nat) (hooksKind ty metadata : Data) (variant : Nat)
    (slots : List Data)
    (address : C.dereference w reference = some ⟨a,i,[]⟩)
    (cell : s.cells ⟨a,i,[]⟩ = some (PV_THR2_KeyValues.pack hooksKind
      [.object [("thread-aggregate-kind",.object [("Adt",.array [ty,.number variant,metadata])]),
        ("thread-aggregate-slots",.array slots)]])) :
    PV_THR2_LibrarySemantics_CellTake641 C [reference] s w =
      some (write s ⟨a,i,[]⟩ (some (PV_THR2_KeyValues.pack hooksKind
        [PV_THR2_KeyValues.pack (.object [("Adt",.array [ty,.number 0,metadata])]) []]))) := by
  have received : receiver C s w reference = some (⟨a,i,[]⟩,
      PV_THR2_KeyValues.pack hooksKind
        [.object [("thread-aggregate-kind",.object [("Adt",.array [ty,.number variant,metadata])]),
          ("thread-aggregate-slots",.array slots)]]) := by
    unfold PV_THR2_SourceStoreLibrary.receiver
    rw [address]
    change (readAddress C s ⟨a,i,[]⟩).bind _ = _
    change ((s.cells ⟨a,i,[]⟩).bind _).bind _ = _
    rw [cell]
    rfl
  unfold PV_THR2_LibrarySemantics_CellTake641
  change (receiver C s w reference).bind _ = _
  rw [received]
  rfl

#print axioms PV_THR2_LibrarySemantics_CellSetPrefix504
#print axioms PV_THR2_LibrarySemantics_CellBoolSet504
#print axioms PV_THR2_LibrarySemantics_CellTake641
#print axioms PV_THR2_LibrarySemantics_CellNew371
#print axioms scalar_set
#print axioms take_root
end PV_LIB_A_CellSourceV2
