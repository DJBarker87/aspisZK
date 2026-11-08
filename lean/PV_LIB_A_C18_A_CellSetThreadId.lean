import PV_LIB_A_CellSetMetadata
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_CellSetThreadId
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_THR2_SourceStoreLibrary PV_LIB_A_CellSetBegin

/-- Exact emitted Option<ThreadId83>. Pinned std/thread/id.rs derives Copy
for ThreadId(NonZero<u64>); Option's drop only drops its selected payload.
This named source interpretation does NOT assert arbitrary Option<T> purity. -/
def optionThreadId (d : Destructor) : Bool :=
  match d.type with
  | .object [("Adt",.object [("id",.object [("Adt",.number 17)]),
      ("generics",.object [("regions",.array []),
        ("types",.array [.object [("Adt",.object [("id",.object [("Adt",.number 83)]),
          ("generics",.object [("regions",.array []),("types",.array []),
            ("const_generics",.array []),("trait_refs",.array [])])])]]),
        ("const_generics",.array []),("trait_refs",.array [])])])] =>
    implId d.witness == some 14
  | _ => false

/-- Recognition reads the call's T and Destruct metadata, never its value.
There is no premise that an arbitrary old T has a trivial destructor. -/
def effectFree (d : Destructor) : Bool := trivial d || optionThreadId d

def PV_THR2_LibrarySemantics_CellSetCopy504 {W : Type} (C : Carrier W Data)
    (fn : Data) (args : List Data) (s : Store Data) (w : W) : Option (Store Data) := do
  let prepared ← PV_THR2_LibrarySemantics_CellSetBegin504 C fn args s w
  if effectFree prepared.destructor then some prepared.store else none

theorem emitted477 : optionThreadId PV_LIB_A_CellSetMetadata.d477 = true := rfl

theorem emitted_copy_cases :
    effectFree PV_LIB_A_CellSetMetadata.d417 = true ∧
    effectFree PV_LIB_A_CellSetMetadata.d437 = true ∧
    effectFree PV_LIB_A_CellSetMetadata.d477 = true ∧
    effectFree PV_LIB_A_CellSetMetadata.d629 = true := ⟨rfl,rfl,rfl,rfl⟩

/-- SpawnHooks and untracked T are STILL nontrivial. Retain the checked old
477 result: it concerned the previous bool/tuple recognizer, which is unedited. -/
theorem emitted_nontrivial_cases :
    effectFree PV_LIB_A_CellSetMetadata.d602 = false ∧
    effectFree PV_LIB_A_CellSetMetadata.d762 = false := ⟨rfl,rfl⟩

theorem copy_from_source {W : Type} (C : Carrier W Data) (s post : Store Data)
    (w : W) (fn reference value old : Data) (d : Destructor) (p : Address)
    (metadata : destructor fn = some d)
    (received : receiver C s w reference = some (p,old))
    (replaced : writeAddress C s p (some value) = some post)
    (recognized : effectFree d = true) :
    PV_THR2_LibrarySemantics_CellSetCopy504 C fn [reference,value] s w = some post := by
  unfold PV_THR2_LibrarySemantics_CellSetCopy504
  rw [begin_from_source C s post w fn reference value old d p metadata received replaced]
  change (if effectFree d = true then some post else none) = _
  rw [recognized]
  rfl

#print axioms optionThreadId
#print axioms effectFree
#print axioms PV_THR2_LibrarySemantics_CellSetCopy504
#print axioms emitted477
#print axioms emitted_copy_cases
#print axioms emitted_nontrivial_cases
#print axioms copy_from_source
end PV_LIB_A_CellSetThreadId
