import LPs_ExpandDomain
set_option autoImplicit false
namespace AspisR1.LPs_ProducerTotal
open Aeneas Aeneas.Std Result

/-- Every caller-shaped compact/initial pair has an expansion trace and the
exact native expansion result. Its byte output is constructed, never assumed.
The check success remains an actual input observation for checked callers. -/
theorem expansion (compact initial : Slice U8)
    (len : compact.val.length=464) (size : initial.val.length=928) :
    ∃ y1 : Slice U8, LPn.Expand.NativeTrace compact.val initial.val 29 y1.val ∧
      y1.val.length=928 ∧ LPs_ExpandDomain.Expanded compact.val y1.val ∧
      _root_.compact.expand_values compact initial=ok (.Ok (),y1) := by
  obtain ⟨after,trace⟩ := LPn.Expand.total compact.val initial.val 29
  have length := LPl.Expand.length _ _ _ _ (LPn.Expand.to_inherited _ _ _ _ trace)
  let y1 : Slice U8 := ⟨after,by rw [length];exact initial.property⟩
  exact ⟨y1,trace,LPs_ExpandDomain.expanded compact initial y1 len size trace⟩

#print axioms expansion
end AspisR1.LPs_ProducerTotal
