import NEF_SemanticRef.Funs
set_option autoImplicit false
namespace NEF_SemanticObserver
open Aeneas Aeneas.Std Result
/-- detail-phases is absent in the deployed graph; even an arbitrary callback
cannot be reached by this helper. No Kani pointer-valued property is used. -/
theorem release_no_effect
    (obs : Option (NEF_SemanticRef.verifier.Phase → Result Unit)) (i : U8) :
    NEF_SemanticRef.mark obs i = ok () := rfl

theorem result_frame {R : Type}
    (obs : Option (NEF_SemanticRef.verifier.Phase → Result Unit)) (i : U8)
    (r : Result R) :
    (do let _ ← NEF_SemanticRef.mark obs i; r) = r := rfl
#print axioms release_no_effect
#print axioms result_frame
end NEF_SemanticObserver
