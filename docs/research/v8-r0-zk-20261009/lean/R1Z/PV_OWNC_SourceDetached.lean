import R1Z.PV_OWNC_GuardCleanup
set_option autoImplicit false
namespace R1Z.PV_OWNC_SourceDetached
open PV_OWNB_Cursor PV_OWNC_GuardState PV_OWN_Operations PV_W_Threading
/-- Once the guard owns storage and cap=0, IntoIter::Drop's RawVec has no
allocation. The saved tail is POD. This models actual no-op glue, not a claim
that a potentially panicking destructor is harmless. -/
def sourceDrop {S X E : Type} (header : PV_OWNC_SourceIterator.Header)
 (freeSource : Action S X E Unit) : Action S X E Unit :=
 if header.cap=0 then dropPod else freeSource

theorem reset_no_free {S X E : Type} (h : PV_OWNC_SourceIterator.Header)
 (freeSource : Action S X E Unit) (w : State S X) :
 sourceDrop (reset h) freeSource w=⟨.ok (),w,[]⟩ := rfl

theorem consumed_no_free {S X E : Type} (q : Cursor) (dst : Nat)
 (glue : PV_OWN_Heap.Token → Action S X E Unit) (s : S) (x : X) :
 dropOwned q.owner glue ⟨(handoff q dst).memory,s,x⟩=
 ⟨.ok (),⟨take q.owner (handoff q dst).memory,s,x⟩,[]⟩ := by
 simp only [dropOwned,PV_OWNC_GuardTransfer.source_consumed]
#print axioms reset_no_free
#print axioms consumed_no_free
end R1Z.PV_OWNC_SourceDetached
