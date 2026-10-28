import NDD_Reference.Funs
import AspisR1SemanticCallExtraction.Funs
import RawPoseidonExtensionSlice
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_Reduce
/-- Total Result equality; in particular valid on the native <2^62 domain. -/
theorem reduce_reference (x : U64) :
    NDD_Reference.reduce_u62_ref x =
      AspisR1SemanticCallExtraction.aspis_core.field.reduce_u64 x := by
  simp only [NDD_Reference.reduce_u62_ref,
    AspisR1SemanticCallExtraction.aspis_core.field.reduce_u64,
    AspisR1SemanticCallExtraction.aspis_core.field.P]
  rfl
theorem reduce_cohort (x : U64) :
    NDD_Reference.reduce_u62_ref x =
      AspisR1SelectedMaskProbe.field.M31.reduce_u62 x := by
  simp only [NDD_Reference.reduce_u62_ref,
    AspisR1SelectedMaskProbe.field.M31.reduce_u62,
    AspisR1SelectedMaskProbe.field.reduce_u64,
    AspisR1SelectedMaskProbe.field.P]
  rfl
#print axioms reduce_reference
#print axioms reduce_cohort
end NDD_Reduce
