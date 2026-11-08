import PV_LIB_SPEC_LaneA_A_StoreActionTable
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_CellSetBegin
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_THR2_SourceStoreLibrary

/-- Read an emitted record without discarding its remaining metadata. -/
def member (key : String) : Data → Option Data
  | .object fields => (fields.find? (fun p => p.1 == key)).map Prod.snd
  | _ => none

structure Destructor where
  type : Data
  witness : Data

/-- The set call's actual T and Destruct witness, including UntrackedDestruct.
No inference from the replacement value or from function id alone. -/
def destructor (fn : Data) : Option Destructor := do
  let regular ← member "Regular" fn
  let generics ← member "generics" regular
  let .array [ty] ← member "types" generics | none
  let .array [witness] ← member "trait_refs" generics | none
  pure ⟨ty,witness⟩

def implId (witness : Data) : Option Nat := do
  let kind ← member "kind" witness
  let impl ← member "TraitImpl" kind
  let .number n ← member "id" impl | none
  pure n

def noop (witness : Data) : Bool :=
  match member "kind" witness with
  | some (.object [("BuiltinOrAuto",.object [("builtin_data",.atom "NoopDestruct"),
      ("parent_trait_refs",.array []),("types",.array [])])]) => true
  | _ => false

/-- Only the two concrete trivial types actually emitted at504 are recognized.
In particular Option/SpawnHooks/UntrackedDestruct never become no-op drops. -/
def trivial (d : Destructor) : Bool :=
  match d.type with
  | .object [("Literal",.atom "Bool")] => noop d.witness
  | .object [("Adt",.object [("id",.atom "Tuple"),("generics",.object
      [("regions",.array []),("types",.array
        [.object [("Literal",.object [("UInt",.atom "Usize")])],
         .object [("Literal",.atom "Bool")]]),
       ("const_generics",.array []),("trait_refs",.array [])])])] =>
    implId d.witness == some 137
  | _ => false

structure Prepared where
  store : Store Data
  old : Data
  destructor : Destructor

/-- core/cell.rs433–438 on pinned1.94.1: replace first, then destroy the OLD T.
This is the start transition, not a whole-call model of a nontrivial Drop.
The saved old value and exact type/witness must survive any pending destructor.
There is no caller-supplied Store transformer or no-destructor assumption. -/
def PV_THR2_LibrarySemantics_CellSetBegin504 {W : Type} (C : Carrier W Data)
    (fn : Data) (args : List Data) (s : Store Data) (w : W) : Option Prepared := do
  let d ← destructor fn
  match args with
  | [reference,value] =>
    let (p,old) ← receiver C s w reference
    let post ← writeAddress C s p (some value)
    pure ⟨post,old,d⟩
  | _ => none

/-- Complete store projection for the recognized trivial destructor cases.
Unsupported typed destruction is explicit, rather than replaced by identity. -/
def PV_THR2_LibrarySemantics_CellSetTrivial504 {W : Type} (C : Carrier W Data)
    (fn : Data) (args : List Data) (s : Store Data) (w : W) : Option (Store Data) := do
  let prepared ← PV_THR2_LibrarySemantics_CellSetBegin504 C fn args s w
  if trivial prepared.destructor then some prepared.store else none

/-- Symbolic source transition; aggregate new values are unrestricted. -/
theorem begin_from_source {W : Type} (C : Carrier W Data) (s post : Store Data)
    (w : W) (fn reference value old : Data) (d : Destructor) (p : Address)
    (metadata : destructor fn = some d)
    (received : receiver C s w reference = some (p,old))
    (replaced : writeAddress C s p (some value) = some post) :
    PV_THR2_LibrarySemantics_CellSetBegin504 C fn [reference,value] s w =
      some ⟨post,old,d⟩ := by
  unfold PV_THR2_LibrarySemantics_CellSetBegin504
  rw [metadata]
  change (receiver C s w reference).bind _ = _
  rw [received]
  change (writeAddress C s p (some value)).bind _ = _
  rw [replaced]
  rfl

/-- No full native reply is needed to perform or describe the replacement.
Consequently the snapshot has the same old value on every answer. -/
theorem old_retained {W : Type} (C : Carrier W Data) (s post : Store Data)
    (w : W) (fn reference value old : Data) (d : Destructor) (p : Address)
    (metadata : destructor fn = some d)
    (received : receiver C s w reference = some (p,old))
    (replaced : writeAddress C s p (some value) = some post) :
    (PV_THR2_LibrarySemantics_CellSetBegin504 C fn [reference,value] s w).map
      (fun prepared => (prepared.old,prepared.destructor.type,prepared.destructor.witness)) =
      some (old,d.type,d.witness) := by
  rw [begin_from_source C s post w fn reference value old d p metadata received replaced]
  rfl

#print axioms member
#print axioms destructor
#print axioms trivial
#print axioms PV_THR2_LibrarySemantics_CellSetBegin504
#print axioms PV_THR2_LibrarySemantics_CellSetTrivial504
#print axioms begin_from_source
#print axioms old_retained
end PV_LIB_A_CellSetBegin
