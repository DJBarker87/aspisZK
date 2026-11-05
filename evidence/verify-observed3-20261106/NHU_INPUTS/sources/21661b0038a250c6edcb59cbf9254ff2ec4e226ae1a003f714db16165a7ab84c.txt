import NHG_COMBINED_IMPORT
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHU_Mark
/-- The adopted deployed body has no profiling effect. Native source
association is the separately pinned NEF observer certificate under (z)(1).
This theorem observes no function-pointer value. -/
theorem result (i : U8) : VerifyPrefix.mark none i = ok () := rfl

/-- Removing the mark preserves the complete following Result, including
Rust errors and ambient failure/divergence. -/
theorem frame {A : Type} (i : U8) (next : Result A) :
 (do VerifyPrefix.mark none i; next) = next := rfl

/-- With the existing chronological carrier, the no-op emits nothing. -/
theorem effects {A : Type} (i : U8)
 (next : AspisR1PublicPreparation.PreparedHashCode.Code A) :
 AspisR1PublicPreparation.PreparedHashCode.run
  (.step (VerifyPrefix.mark none i) (fun _ => next)) =
 AspisR1PublicPreparation.PreparedHashCode.run next := rfl
#print axioms result
#print axioms frame
#print axioms effects
end AspisR1.NHU_Mark
