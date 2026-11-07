import PV_LIB_SLICE_Spec_f13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SLICE_Statements
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER
/-- Column descriptors and capture/buffer roots are chosen at call entry. -/
structure ArrayEntry extends Entry where
  columns : Fin 16 → Source
  arrayAddress : Address
  capture : Address
  buffer : Address
  index : Fin 16

def sources (e : ArrayEntry) : List Source := List.ofFn e.columns

def column (root : Address) (i : Nat) : Data :=
  PV_STX2_Aggregates.pack (PV_STX2_SliceClosureStores.kind PV_STX2_SliceF2.node10)
    [PV_STX2_SliceArrayInterpretation.elementPointer root i]
def wrapper (root : Address) (i : Nat) : Data :=
  PV_STX2_Aggregates.pack (PV_STX2_SliceClosureStores.kind PV_STX2_SliceF2.node13) [column root i]
def wrappedValue (v : Data) : Data :=
  PV_STX2_Aggregates.pack (PV_STX2_SliceClosureStores.kind PV_STX2_SliceF8.node11) [v]

/-- Read only the actual entry array and descriptors, never future reads. -/
def ArrayPre (m : Machine) (c : Config) (e : ArrayEntry) : Prop :=
  Pre c e.toEntry ∧
  readAddress m.carrier c.store e.arrayAddress =
    some (.array (List.ofFn (fun i => vector (e.columns i).header))) ∧
  (∀ i, (e.columns i).Valid m c e.toEntry ∧
    (e.columns i).descriptor = {e.arrayAddress with fields := e.arrayAddress.fields ++ [i.val]})

/-- Source index is paired with the source capture at entry. -/
def CapturePre (m : Machine) (c : Config) (e : ArrayEntry) (wrapped : Bool) : Prop :=
  ArrayPre m c e ∧ e.capture.activation < c.frame.activation ∧
  ¬ inRoot e.capture e.arrayAddress ∧
  readAddress m.carrier c.store e.capture =
    some (if wrapped then wrapper e.arrayAddress e.index.val else column e.arrayAddress e.index.val)

/-- Sixteen independent fresh OWNER ids in column order; zero-length Vecs may
share the aligned dangling address but never their fresh OWNER identity. -/
def ArrayClone (r : Resources) (enc : Encode) (g : PV_OWN2_FreshAllocation.GrantedRegions)
    (e : ArrayEntry) (out : Prefix OWNER Event) (v : Data) : Prop :=
  ∃ values : Fin 16 → Data, ∃ ids : Fin 16 → Nat, ∃ headers : Fin 16 → PV_EVHB_RawVecOwner.Header,
    v = .array (List.ofFn values) ∧
    (∀ i, Clone r enc g e.toEntry (e.columns i) out (values i) ∧
      e.owner.next ≤ ids i ∧ values i = vector (headers i) ∧
      ∃ q, PV_EVHB_OWNER.receiver out.world q = some (ids i,headers i) ∧
        PV_OWN2_ExportContracts.VecOwnership (Attr := Unit) (Data := Data) (Native := Unit)
          (IoError := Unit) (OsString := Unit) (Scope := Unit) r enc g out.world
          (e.columns i).region q (e.columns i).identity (ids i) (e.columns i).header (headers i)) ∧
    (∀ i j, i ≠ j → ids i ≠ ids j) ∧
    (∀ i j, i ≠ j → (headers i).len > 0 → (headers j).len > 0 →
      (headers i).pointer + (headers i).len*4 ≤ (headers j).pointer ∨
      (headers j).pointer + (headers j).len*4 ≤ (headers i).pointer)
#print axioms ArrayPre
#print axioms CapturePre
#print axioms ArrayClone
end PV_LIB_SLICE_Statements

namespace PV_LIB_SLICE_Spec_f6
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER PV_LIB_SLICE_Statements
abbrev Entry := ArrayEntry
abbrev MachineSpec := PV_LIB_SLICE_Statements.MachineSpec
abbrev start (e : Entry) := PV_LIB_SLICE_Statements.start PV_STX2_SliceF6.program
  [PV_STX2_TypedReferences.reference e.capture .null,PV_STX2_SliceLoopCallback.indexTuple e.index.val] e.toEntry

def Pre (m : Machine) (e : Entry) : Prop := CapturePre m (start e) e false

def Post (r : Resources) (enc : Encode) (g : PV_OWN2_FreshAllocation.GrantedRegions)
    (m : Machine) (e : Entry) (impl : Outcome) : Prop :=
  PV_LIB_SLICE_Statements.Post r enc m (start e) e.toEntry (sources e) [e.capture]
    (fun out v => Clone r enc g e.toEntry (e.columns e.index) out v ∧
      readAddress m.carrier (PV_STX2_ToVecCallCallerPost.statusStore out.status) e.capture =
        some (column e.arrayAddress (e.index.val+1))) impl

def Contract (r : Resources) (enc : Encode) (g : PV_OWN2_FreshAllocation.GrantedRegions)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend)
    (env : Environment) (impl : Machine → Entry → Outcome) : Prop :=
  ∀ m, MachineSpec m base ctrl external backend r enc env → ∀ e, Pre m e → Post r enc g m e (impl m e)
#print axioms Pre
#print axioms MachineSpec
#print axioms Post
#print axioms Contract
end PV_LIB_SLICE_Spec_f6
