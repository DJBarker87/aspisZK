import PV_LIB_A_ArcDropCompare10
import PV_LIB_A_FetchSubSource10
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_StrongCount10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable

/-- Actual ArcInner layout, with the provider's exact AtomicUsize wrapper. -/
def inner (weak payload atomicKind unsafeKind : Data) (strong : Nat) : Data :=
  PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
    [PV_FN_THREAD_f360Outcomes.atomicValue atomicKind unsafeKind strong,weak,payload]

def site (child heap localIndex : Nat) (ordering : Data) : SourceSite :=
  let args := [PV_STX2_TypedReferences.reference ⟨heap,localIndex,[0]⟩ .null,.number 1,ordering]
  ⟨.inherited (.primitive .fetchSub581),PV_LIB_A_ArcDropCompare10.call.1,
    PV_LIB_A_ArcDropCompare10.wait child args,args⟩

theorem read_count (C : Carrier OWNER Data) (b : Bool) (s : Store Data)
    (a i n : Nat) (weak payload atomicKind unsafeKind : Data)
    (source : s.cells ⟨a,i,[]⟩ = some (inner weak payload atomicKind unsafeKind n)) :
    readAddress (PV_LIB_A_DestructorValues10.carrier C b) s ⟨a,i,[0,0,0]⟩ = some (.number n) := by
  change (s.cells ⟨a,i,[]⟩).bind _ = _
  rw [source]
  rfl

theorem write_count (C : Carrier OWNER Data) (b : Bool) (s : Store Data)
    (a i n replacement : Nat) (weak payload atomicKind unsafeKind : Data)
    (source : s.cells ⟨a,i,[]⟩ = some (inner weak payload atomicKind unsafeKind n)) :
    writeAddress (PV_LIB_A_DestructorValues10.carrier C b) s ⟨a,i,[0,0,0]⟩
      (some (.number replacement)) =
      some (write s ⟨a,i,[]⟩ (some (inner weak payload atomicKind unsafeKind replacement))) := by
  change (s.cells ⟨a,i,[]⟩).bind _ = _
  rw [source]
  rfl

/-- At actual486's581 boundary the old-value snapshot reads the source strong
field from its provider representation; it is not a caller-supplied count. -/
theorem snapshot (C : Carrier OWNER Data) (b : Bool) (c : Config) (w : OWNER)
    (child heap localIndex n : Nat) (ordering weak payload atomicKind unsafeKind : Data)
    (source : c.store.cells ⟨heap,localIndex,[]⟩ =
      some (inner weak payload atomicKind unsafeKind n)) :
    PV_LIB_A_FetchSubReply10.readOld (PV_LIB_A_DestructorValues10.carrier C b)
      c w (site child heap localIndex ordering) = some n := by
  apply PV_LIB_A_FetchSubSource10.read_source
    (p := ⟨heap,localIndex,[0]⟩) (n := 1)
  · rfl
  · exact PV_LIB_A_DestructorValues10.reference C b _ _ w
  · exact read_count C b c.store heap localIndex n weak payload atomicKind unsafeKind source

/-- The actual emitted call token is absent from the typed-body override,
regardless of the fallback resolver. No generic metadata is erased here. -/
theorem native_table (P : Data → Option PV_STX2_SliceSyntax.Program) :
    v2ProvenancePrograms P PV_LIB_A_ArcDropCompare10.call.1 = P PV_LIB_A_ArcDropCompare10.call.1 := rfl

/-- A local selector fact at the original21732 wait. The actual resolver's
native classification is a source-program-table fact, never an old-count law. -/
theorem selected (P : Data → Option PV_STX2_SliceSyntax.Program) (c : Config)
    (child heap localIndex : Nat) (ordering : Data)
    (completed : c.frame.completed = none)
    (waiting : c.frame.waiting = some (site child heap localIndex ordering).waiting)
    (native : P PV_LIB_A_ArcDropCompare10.call.1 = none) :
    PV_LIB_A_FetchSubReply10.selected P c = some (site child heap localIndex ordering) := by
  have action : v2Source PV_LIB_A_ArcDropCompare10.call.1 =
      some (.inherited (.primitive .fetchSub581)) := rfl
  simp [PV_LIB_A_FetchSubReply10.selected,sourceSelect,completed,waiting,
    site,PV_LIB_A_ArcDropCompare10.wait,native_table,native,action,
    PV_LIB_A_ArcDropCompare10.function]

#print axioms inner
#print axioms site
#print axioms read_count
#print axioms write_count
#print axioms snapshot
#print axioms native_table
#print axioms selected
end PV_LIB_A_StrongCount10
