import NEF_TailRef.Funs
set_option autoImplicit false
namespace NEF_ExtractedTail
open Aeneas Aeneas.Std Result NEF_TailRef
/-- Generic A and B retain the entire actual accumulator and pending carrier;
there is no empty-Vec, limb-canonicality or successful-prefix premise here. -/
theorem query_values_tail {A B : Type} (a : A) (pending : B) (i : Usize) :
    query_tail a pending i none = ok (core.result.Result.Ok (a,pending)) := rfl

theorem contextual {A B R : Type} (a : A) (pending : B) (i : Usize)
    (k : core.result.Result (A × B) NEF_TailRef.Error → Result R) :
    (do let r ← query_tail a pending i none; k r) =
      k (core.result.Result.Ok (a,pending)) := rfl

theorem external_frame {A B S E : Type} (a : A) (pending : B) (i : Usize)
    (state : S) (effects : List E) :
    (query_tail a pending i none,state,effects) =
      (ok (core.result.Result.Ok (a,pending)),state,effects) := rfl
#print axioms query_values_tail
#print axioms contextual
#print axioms external_frame
end NEF_ExtractedTail
