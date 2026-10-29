import NEF_ObserverRef.Funs
import NEF_ObserverEffects
set_option autoImplicit false
namespace NEF_ExtractedObserver
open Aeneas Aeneas.Std Result

theorem observer_none : NEF_ObserverRef.observer = ok none := rfl

theorem mark_none (p : NEF_ObserverRef.verifier.Phase) :
    NEF_ObserverRef.verifier.mark none p = ok () := rfl

theorem release_mark (p : NEF_ObserverRef.verifier.Phase) :
    NEF_ObserverRef.release_mark p = ok () := rfl

/-- Any continuation sees precisely its original Result, including failures.
The mark's own emitted Result is ok and has no callback call. -/
theorem result_frame {R : Type} (p : NEF_ObserverRef.verifier.Phase)
    (reply : Result R) :
    (do let _ ← NEF_ObserverRef.release_mark p; reply) = reply := by
  rw [release_mark]
  rfl

theorem complete_frame {R S E : Type} (p : NEF_ObserverRef.verifier.Phase)
    (s : S) (reply : Result R) (events : List E) :
    ((do let _ ← NEF_ObserverRef.release_mark p; reply),s,events) =
    (reply,s,events) := by
  rw [result_frame]
#print axioms observer_none
#print axioms mark_none
#print axioms release_mark
#print axioms result_frame
#print axioms complete_frame
end NEF_ExtractedObserver
