import R1Z.PV_OWNB_CursorCleanup
set_option autoImplicit false
namespace R1Z.PV_OWNB_CursorExit
open PV_OWNB_Cursor PV_OWN_Operations PV_W_Threading
/-- Rust Result error returns run owned cleanup before returning the error.
The deallocation primitive's failure/divergence keeps its exact post-world. -/
def error {S X E A : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (q : Cursor) (e : E) : Action S X E A :=
 bind (PV_OWNB_CursorCleanup.cleanup dealloc q) (fun _=>lift (.fail e))

/-- An abort handler is invoked directly, with no fabricated unwind suffix. -/
def abort {S X E A : Type} (handler : Action S X E A) : Action S X E A := handler

theorem error_success {S X E A : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (q : Cursor) (e : E) (w : State S X)
 (h:(PV_OWNB_CursorCleanup.cleanup dealloc q w).outcome=.ok ()) :
 error (A:=A) dealloc q e w=
 ⟨.fail e,(PV_OWNB_CursorCleanup.cleanup dealloc q w).world,
 (PV_OWNB_CursorCleanup.cleanup dealloc q w).calls⟩ := by
 simp [error,PV_W_Threading.bind,h,lift]

theorem error_failure {S X E A : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (q : Cursor) (e f : E) (w : State S X)
 (h:(PV_OWNB_CursorCleanup.cleanup dealloc q w).outcome=.fail f) :
 error (A:=A) dealloc q e w=
 ⟨.fail f,(PV_OWNB_CursorCleanup.cleanup dealloc q w).world,
 (PV_OWNB_CursorCleanup.cleanup dealloc q w).calls⟩ := bind_fail _ _ w f h

theorem error_divergence {S X E A : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (q : Cursor) (e : E) (w : State S X)
 (h:(PV_OWNB_CursorCleanup.cleanup dealloc q w).outcome=.div) :
 error (A:=A) dealloc q e w=
 ⟨.div,(PV_OWNB_CursorCleanup.cleanup dealloc q w).world,
 (PV_OWNB_CursorCleanup.cleanup dealloc q w).calls⟩ := bind_div _ _ w h

theorem abort_exact {S X E A : Type} (handler : Action S X E A) (w : State S X) :
 abort handler w=handler w := rfl
#print axioms error_success
#print axioms error_failure
#print axioms error_divergence
#print axioms abort_exact
end R1Z.PV_OWNB_CursorExit
