import PV_LIB_SPEC_LaneA_A_CellSourceV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_DropStoreV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_THR2_SourceStoreLibrary PV_LIB_A_StorePrimitiveV2

/-- Nonlast Arc/Weak count transition. Reading the count, rather than a desired
store or caller-supplied no-drop predicate, selects this source branch. Last
references, dangling Weak, payload Drop and deallocation are unsupported here. -/
def nonlast {W : Type} (C : Carrier W Data) (args : List Data)
    (s : Store Data) (w : W) (field : Nat) : Option (Store Data) := do
  let p ← PV_LIB_A_ArcStoreV2.inner C args s w
  let count : Address := {p with fields := p.fields ++ [field,0,0]}
  let n ← numberAt C s count
  if 1 < n then writeAddress C s count (some (.number (n-1))) else none

/-- alloc/sync.rs Arc::drop486: when fetch_sub returns >1, return immediately;
no payload destructor or weak decrement runs. Native/world/order binding open. -/
def PV_THR2_LibrarySemantics_ArcDropNonlast486 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) :=
  nonlast C args s w 0

/-- alloc/sync.rs Weak::drop683: the nonlast allocated Weak branch decrements
weak and does not deallocate. The dangling/last branches remain unsupported. -/
def PV_THR2_LibrarySemantics_WeakDropNonlast683 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) :=
  nonlast C args s w 1

/-- Option::take369's source None reuses the old emitted type/generic metadata.
There is no Drop(old T): the old value is moved to the return value. -/
def emptyOption : Data → Option Data
  | .object [("thread-aggregate-kind",.object [("Adt",.array [ty,.number _,metadata])]),
      ("thread-aggregate-slots",.array _)] =>
    some (PV_THR2_KeyValues.pack (.object [("Adt",.array [ty,.number 0,metadata])]) [])
  | _ => none

def PV_THR2_LibrarySemantics_OptionTake369 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) := do
  match args with
  | [reference] =>
    let (p,old) ← receiver C s w reference
    let empty ← emptyOption old
    writeAddress C s p (some empty)
  | _ => none

theorem none_from_source (ty metadata : Data) (variant : Nat) (slots : List Data) :
    emptyOption (PV_THR2_KeyValues.pack (.object [("Adt",.array [ty,.number variant,metadata])]) slots) =
      some (PV_THR2_KeyValues.pack (.object [("Adt",.array [ty,.number 0,metadata])]) []) := rfl

#print axioms PV_THR2_LibrarySemantics_ArcDropNonlast486
#print axioms PV_THR2_LibrarySemantics_WeakDropNonlast683
#print axioms PV_THR2_LibrarySemantics_OptionTake369
#print axioms none_from_source
end PV_LIB_A_DropStoreV2
