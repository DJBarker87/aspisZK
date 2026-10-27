import LPt_LPs_ExpandDomain
import LPs_PreparedClaim
set_option autoImplicit false
namespace AspisR1.LPt_ByteDomain
open Aeneas Aeneas.Std Result

/-- The two producer predicates are converted in this same environment, on the
same input and output bytes. No decoder-success premise is supplied. -/
theorem natural (compact before y1 : Slice U8)
    (len : compact.val.length=464) (size : before.val.length=928)
    (checked : LPt_External.compact.check_values compact=ok (.Ok ()))
    (trace : LPt_LPn.Expand.NativeTrace compact.val before.val 29 y1.val) :
    y1.val.length=928 ∧ LPq_ExpandedWords.Expanded compact.val y1.val ∧
      LPq_ExpandedWords.CompactCanonical compact.val := by
  obtain ⟨length,expanded,_⟩ := LPt_LPs_ExpandDomain.expanded compact before y1 len size trace
  exact ⟨length,expanded,LPt_LPs_CheckDomain.checked compact len checked⟩

theorem checked_expanded (compact before y1 : Slice U8)
    (len : compact.val.length=464) (size : before.val.length=928)
    (checked : LPt_External.compact.check_values compact=ok (.Ok ()))
    (trace : LPt_LPn.Expand.NativeTrace compact.val before.val 29 y1.val) :
    LPq_SelectedDomain.ByteDomain y1 := by
  obtain ⟨length,expanded,canonical⟩ := natural compact before y1 len size checked trace
  exact LPs_NaturalDomain.selected compact y1 length expanded canonical

#print axioms natural
#print axioms checked_expanded
end AspisR1.LPt_ByteDomain
