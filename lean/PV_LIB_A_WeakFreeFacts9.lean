import PV_LIB_A_WeakOwnerFree9
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakFreeFacts9
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_WeakOwnerFree9

/-- Once source allocator/backing reads are derived, poll is the actual free
primitive followed by the existing exact source/return administration. -/
theorem poll_graph (C : Carrier OWNER Data) (resources : Resources) (encode : Encode)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (p : Address) (unit : Data)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Unit)
    (allocator : weakAllocator C c w site = some ())
    (sourceUnit : C.aggregate PV_LIB_A_GenericDropMachine.unitTag [] = some unit)
    (resource : PV_LIB_A_AllocationBacking9.deallocate resources encode w p = some r) :
    poll C resources encode c w es stack site p =
      sourceReceive C c es stack site (.deallocate p) (reply unit r) := by
  simp only [poll,allocator,sourceUnit,resource]

/-- A pending allocator preserves the source block and saved weak count.
Its next poll is a free retry (WeakOwnerFree9.retry), not WeakDropBegin683. -/
theorem pending (C : Carrier OWNER Data) (resources : Resources) (encode : Encode)
    (c : Config) (w post : OWNER) (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (p : Address) (unit : Data)
    (allocator : weakAllocator C c w site = some ())
    (sourceUnit : C.aggregate PV_LIB_A_GenericDropMachine.unitTag [] = some unit)
    (resource : PV_LIB_A_AllocationBacking9.deallocate resources encode w p =
      some ⟨.pending,post,events⟩) :
    poll C resources encode c w es stack site p =
      ⟨⟨⟨.running c,post,es ++ events⟩,stack⟩,some (site,.deallocate p)⟩ := by
  rw [poll_graph C resources encode c w es stack site p unit _ allocator sourceUnit resource]
  exact source_pending C c es events stack site (.deallocate p) post

/-- On the success branch only, source-block clearing occurs on the SAME
post-world and event suffix as the resource's actual free. No final Store is
supplied as a destructor or callback meaning. -/
theorem success (C : Carrier OWNER Data) (resources : Resources) (encode : Encode)
    (c : Config) (w post : OWNER) (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (a i : Nat) (unit : Data)
    (allocator : weakAllocator C c w site = some ())
    (sourceUnit : C.aggregate PV_LIB_A_GenericDropMachine.unitTag [] = some unit)
    (resource : PV_LIB_A_AllocationBacking9.deallocate resources encode w ⟨a,i,[]⟩ =
      some ⟨.returned (.ok ()),post,events⟩) :
    (poll C resources encode c w es stack site ⟨a,i,[]⟩).base =
      let q := PV_THR2_ChildBoundary.delivered C
        {c with store := write c.store ⟨a,i,[]⟩ none} site.waiting
        ⟨.returned (.ok unit),post,events⟩
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  rw [poll_graph C resources encode c w es stack site ⟨a,i,[]⟩ unit _
    allocator sourceUnit resource]
  rfl

/-- Every failed/diverging/faulting resource reply retains the entire source
store before ordinary caller delivery, rather than clearing the block early. -/
theorem non_success_source (C : Carrier OWNER Data) (p : Address) (s : Store Data)
    (unit : Data) (r : Reply OWNER PV_RJ4IDB.NativeEvent Unit)
    (notReturned : ∀ v, r.answer ≠ .returned (.ok v)) :
    PV_LIB_A_WeakDropSource.finish C (.deallocate p) s (reply unit r) = some s := by
  cases ha : r.answer with
  | pending => simp only [reply,ha,PV_LIB_A_WeakDropSource.finish]
  | fault f => simp only [reply,ha,PV_LIB_A_WeakDropSource.finish]
  | returned result =>
    cases result with
    | fail e => simp only [reply,ha,PV_LIB_A_WeakDropSource.finish]
    | div => simp only [reply,ha,PV_LIB_A_WeakDropSource.finish]
    | ok v => exact False.elim (notReturned v ha)

/-- Custom or erased allocators never become Global through a source pointer.
The type check precedes dereference, and the exact tagged value is then checked. -/
theorem erased_allocator (C : Carrier OWNER Data) (s : Store Data) (w : OWNER) (value : Data) :
    PV_LIB_A_WeakOwnerFree9.allocator C s w
      (.object [("Error",.atom "removed allocator parameter")]) value = none := rfl

#print axioms poll_graph
#print axioms pending
#print axioms success
#print axioms non_success_source
#print axioms erased_allocator
end PV_LIB_A_WeakFreeFacts9
