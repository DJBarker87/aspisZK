import PV_LIB_A_FetchSubReply10
import PV_THR2_LibrarySemantics_AtomicUsizeNew
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_FetchSubSource10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable

/-- Value interpretation cannot alter the existing source subtraction on any
answer, including pending/failure, wrapping or underflow. -/
theorem same_write (C : Carrier OWNER Data) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (fn : Data) (args : List Data) (s : Store Data) (w : OWNER)
    (old : Nat) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) :
    start C values (.inherited (.primitive .fetchSub581)) fn args s w
      (PV_LIB_A_FetchSubReply10.PV_THR2_LibrarySemantics_FetchSubValue581 old r) =
    start C values (.inherited (.primitive .fetchSub581)) fn args s w r := rfl

/-- The snapshot reads the actual typed source reference, before any write.
These are local address/read facts, not a new row or branch precondition. -/
theorem read_source (C : Carrier OWNER Data) (c : Config) (w : OWNER) (site : SourceSite)
    (reference ordering : Data) (n old : Nat) (p : Address)
    (args : site.arguments = [reference,.number n,ordering])
    (pointer : C.dereference w reference = some p)
    (cell : readAddress C c.store {p with fields := p.fields ++ [0,0]} = some (.number old)) :
    PV_LIB_A_FetchSubReply10.readOld C c w site = some old := by
  simp only [PV_LIB_A_FetchSubReply10.readOld,args]
  change (PV_LIB_A_StorePrimitiveV2.atReference C c.store w reference [0,0]).bind _ = _
  unfold PV_LIB_A_StorePrimitiveV2.atReference
  rw [pointer]
  change PV_LIB_A_StorePrimitiveV2.numberAt C c.store
    {p with fields := p.fields ++ [0,0]} = some old
  unfold PV_LIB_A_StorePrimitiveV2.numberAt
  rw [cell]
  rfl

/-- The two exact atomic constructor kinds are the provider's own definition.
Writes are derived over its wrapper, not assumed as a final Store delta. -/
theorem atomic_root_read (C : Carrier OWNER Data) (b : Bool) (s : Store Data)
    (a i old : Nat) (atomicKind unsafeKind : Data)
    (source : s.cells ⟨a,i,[]⟩ = some
      (PV_FN_THREAD_f360Outcomes.atomicValue atomicKind unsafeKind old)) :
    readAddress (PV_LIB_A_DestructorValues10.carrier C b) s ⟨a,i,[0,0]⟩ = some (.number old) := by
  change (s.cells ⟨a,i,[]⟩).bind _ = _
  rw [source]
  rfl

#print axioms same_write
#print axioms read_source
#print axioms atomic_root_read
end PV_LIB_A_FetchSubSource10
