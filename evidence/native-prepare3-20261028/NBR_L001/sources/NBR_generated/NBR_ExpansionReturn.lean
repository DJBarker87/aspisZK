import LPt_LPs_ProducerTotal
set_option autoImplicit false
namespace AspisR1.NBR_ExpansionReturn
open Aeneas Aeneas.Std Result

/-- Identify the arbitrary returned callee carrier with the constructed trace.
The complete callee return observation is required; no chosen successful
output, byte formula or NativeTrace is supplied by the caller. -/
theorem source (compact initial returned : Slice U8)
    (len : compact.val.length=464) (size : initial.val.length=928)
    (call : LPt_External.compact.expand_values compact initial=ok (.Ok (),returned)) :
    LPt_LPn.Expand.NativeTrace compact.val initial.val 29 returned.val ∧
      returned.val.length=928 ∧ LPt_LPs_ExpandDomain.Expanded compact.val returned.val := by
  obtain ⟨out,trace,length,bytes,result⟩ := LPt_LPs_ProducerTotal.expansion compact initial len size
  have same : out=returned := (Prod.mk.inj (Result.ok.inj (result.symm.trans call))).2
  subst out
  exact ⟨trace,length,bytes⟩

/-- A returned error is impossible on the exact caller-shaped domain. -/
theorem no_error (compact initial : Slice U8)
    (len : compact.val.length=464) (size : initial.val.length=928)
    (error : LPt_External.compact.CodecError) (returned : Slice U8) :
    LPt_External.compact.expand_values compact initial≠ok (.Err error,returned) := by
  obtain ⟨out,_,_,_,result⟩ := LPt_LPs_ProducerTotal.expansion compact initial len size
  rw [result]
  intro bad
  cases bad

#print axioms source
#print axioms no_error
end AspisR1.NBR_ExpansionReturn
