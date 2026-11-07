import NNG_SourceSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

/-- Lexical fission of the ACTUAL fresh body; all opaque callees are still
explicit and complete. No native observation or successful child is assumed. -/
theorem emitted {H W : Type} (c : Calls) (s : Parent H W) :
 f_r c s=NNG_Emitted.emitted c s := by rfl
#print axioms emitted
end AspisR1.NNG_SourceSuffixes
