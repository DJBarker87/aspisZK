import LPt_LPs_ExpandDomain
set_option autoImplicit false
namespace AspisR1.LPt_LPs_ProducerTotal
open Aeneas Aeneas.Std Result

/-- Every caller-shaped compact/initial pair has an expansion trace and the
exact native expansion result. Its byte output is constructed, never assumed.
The check success remains an actual input observation for checked callers. -/
theorem expansion (compact initial : Slice U8)
    (len : compact.val.length=464) (size : initial.val.length=928) :
    ∃ y1 : Slice U8, LPt_LPn.Expand.NativeTrace compact.val initial.val 29 y1.val ∧
      y1.val.length=928 ∧ LPt_LPs_ExpandDomain.Expanded compact.val y1.val ∧
      _root_.LPt_External.compact.expand_values compact initial=ok (.Ok (),y1) := by
  obtain ⟨after,trace⟩ := LPt_LPn.Expand.total compact.val initial.val 29
  have length := LPt_LPl.Expand.length _ _ _ _ (LPt_LPn.Expand.to_inherited _ _ _ _ trace)
  let y1 : Slice U8 := ⟨after,by rw [length];exact initial.property⟩
  exact ⟨y1,trace,LPt_LPs_ExpandDomain.expanded compact initial y1 len size trace⟩

#print axioms expansion
end AspisR1.LPt_LPs_ProducerTotal
