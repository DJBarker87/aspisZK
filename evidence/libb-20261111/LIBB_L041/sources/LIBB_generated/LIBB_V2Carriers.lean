import LIB_ErrorDebug
import LIB_Root0
set_option autoImplicit false
noncomputable section
namespace LIBB_V2Carriers
abbrev VErr := LIB_ErrorDebug.VErr
abbrev debug := LIB_ErrorDebug.debug
abbrev Root0 := LIB_Root0.root0
/-- Exact fixed V2 fields reuse modules 3–4; no replacement error or Root0
predicate is introduced by lane B. -/
theorem exact_fields : VErr = LIB_ErrorDebug.VErr ∧
 debug = LIB_ErrorDebug.debug ∧ Root0 = LIB_Root0.root0 := ⟨rfl,rfl,rfl⟩
#print axioms exact_fields
end LIBB_V2Carriers
end
