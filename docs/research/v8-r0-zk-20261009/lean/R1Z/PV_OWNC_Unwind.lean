import R1Z.PV_OWNC_SourceLoop
set_option autoImplicit false
namespace R1Z.PV_OWNC_Unwind
open PV_OWNB_Cursor PV_OWN_Operations PV_W_Threading
/-- On predicate unwind, InPlaceDrop drops only POD headDrop, then IntoIter
owns the unread tail/allocation. After detachment the destination guard owns
that same cleanup instead. Prefix POD glue preserves every failure headDrop. -/
theorem prefix_then_source {S X E : Type}
 (dealloc : Nat → Request → S → Outcome E Unit × S) (q : Cursor) (w : State S X) :
 bind PV_OWNC_GuardCleanup.headDrop (fun _=>PV_OWNB_CursorCleanup.cleanup dealloc q) w=
 PV_OWNB_CursorCleanup.cleanup dealloc q w := by
 simp only [PV_OWNC_GuardCleanup.headDrop,dropPod,lift,bind,List.nil_append]

theorem abort_direct {S X E A : Type} (handler : Action S X E A)
 (unwind : Action S X E Unit) (w : State S X) :
 PV_OWNB_CursorExit.abort handler w=handler w := rfl
#print axioms prefix_then_source
#print axioms abort_direct
end R1Z.PV_OWNC_Unwind
