import XRr_Candidate64
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRr_VecRestoration
/-- Source library restoration carries the returned slice bytes verbatim. -/
theorem source {T : Type} (v : alloc.vec.Vec T) (slice : Slice T)
 (back : Slice T → alloc.vec.Vec T)
 (run : lift (alloc.vec.Vec.deref_mut v)=ok (slice,back)) :
 slice.val=v.val ∧ ∀ next, (back next).val=next.val := by
 cases Result.ok.inj run
 exact ⟨rfl,by intros;rfl⟩
#print axioms source
end XRr_VecRestoration
