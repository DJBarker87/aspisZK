import PV_LIB_A_ArcStoreV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_CellTakeV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_THR2_SourceStoreLibrary PV_LIB_A_StorePrimitiveV2
/-- Exact emitted641 instantiation: T=std::thread::spawnhook::SpawnHooks
(type142, hash-consed20954), whose derived Default has first=None.
Read the existing type metadata; preserve it rather than inventing a tag.
No arbitrary default value or final Store is supplied by an environment. -/
def defaultSpawnHooks : Data → Option Data
  | .object [("thread-aggregate-kind",hooksKind),
      ("thread-aggregate-slots",.array [.array [
        .object [("thread-aggregate-kind",.object [("Adt",.array [ty,.number _,metadata])]),
          ("thread-aggregate-slots",.array _)]]])] =>
    some (PV_THR2_KeyValues.pack hooksKind [PV_THR2_KeyValues.pack
      (.object [("Adt",.array [ty,.number 0,metadata])]) []])
  | _ => none

/-- ONE documented meaning for Cell::take641 at emitted23258: replace the
boxed or local Cell<SpawnHooks> payload by its actual Default value. It does
not drop the old hooks; they are returned by the unchanged full native reply. -/
def PV_THR2_LibrarySemantics_CellTake641 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) := do
  match args with
  | [reference] =>
    let p ← atReference C s w reference [0,0]
    let old ← readAddress C s p
    let empty ← defaultSpawnHooks old
    writeAddress C s p (some empty)
  | _ => none

/-- The type142 constructor with either existing Option discriminant yields
its own source None tag, independently of the old hook payload. -/
theorem default_from_source (hooksKind ty metadata : Data) (variant : Nat)
    (slots : List Data) :
    defaultSpawnHooks (PV_THR2_KeyValues.pack hooksKind
      [.object [("thread-aggregate-kind",.object [("Adt",.array [ty,.number variant,metadata])]),
        ("thread-aggregate-slots",.array slots)]]) =
    some (PV_THR2_KeyValues.pack hooksKind [PV_THR2_KeyValues.pack
      (.object [("Adt",.array [ty,.number 0,metadata])]) []]) := rfl

/-- Source-backed nonempty Weak::drop683 count projection, alloc/sync.rs3468.
The dangling Weak case and deallocation/world correspondence remain separate
binding obligations; this function is NOT installed for arbitrary Weak values. -/
def PV_THR2_LibrarySemantics_WeakDropSource683 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) := do
  let p ← PV_LIB_A_ArcStoreV2.inner C args s w
  let count : Address := {p with fields := p.fields ++ [1,0,0]}
  let n ← numberAt C s count
  writeAddress C s count (some (.number ((n+modulus-1)%modulus)))

/-- Arc::drop486 always decrements strong before the possible last-strong
payload destructor. This is its PREFIX projection, not its complete Store
semantics, so it is not installed as a whole native Arc-drop action. -/
def PV_THR2_LibrarySemantics_ArcDropPrefix486 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) := do
  let p ← PV_LIB_A_ArcStoreV2.inner C args s w
  let count := PV_THR2_LibrarySemantics_ArcClone.countAddress p
  let n ← numberAt C s count
  writeAddress C s count (some (.number ((n+modulus-1)%modulus)))

#print axioms PV_THR2_LibrarySemantics_CellTake641
#print axioms default_from_source
#print axioms PV_THR2_LibrarySemantics_WeakDropSource683
#print axioms PV_THR2_LibrarySemantics_ArcDropPrefix486
end PV_LIB_A_CellTakeV2
