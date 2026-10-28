import NDD_Reference.Funs
import AspisR1SemanticCallExtraction.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_Reduce
/-- Total Result equality; in particular valid on the native <2^62 domain. -/
theorem reduce_reference (x : U64) :
    NDD_Reference.reduce_u62_ref x =
      AspisR1SemanticCallExtraction.aspis_core.field.reduce_u64 x := by
  rfl
#print axioms reduce_reference
end NDD_Reduce
