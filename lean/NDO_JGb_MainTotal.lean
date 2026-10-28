import RPt_FIp_SemanticValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_MainTotal
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic FIp_SemanticValues

theorem add (x y : MQ) (hx : Canon x) (hy : Canon y) :
    ∃ out,FIp_SemanticArithmetic.add x y=ok out ∧ Canon out ∧ decode out=decode x+decode y := by
  obtain ⟨out,call,hc,hv⟩ := ExtractedMaskQM31Exact.current_qm_add_exact (toProbe x) (toProbe y) hx hy
  refine ⟨fromProbe out,?_,?_,?_⟩
  · unfold FIp_SemanticArithmetic.add
    rw [call]
    rfl
  · simpa only [Canon,to_from] using hc
  · exact hv
#print axioms add

theorem mul (x y : MQ) (hx : Canon x) (hy : Canon y) :
    ∃ out,FIp_SemanticArithmetic.mul x y=ok out ∧ Canon out ∧ decode out=decode x*decode y := by
  obtain ⟨out,call,hc,hv⟩ := ExtractedMaskQM31Exact.current_qm_mul_exact (toProbe x) (toProbe y) hx hy
  refine ⟨fromProbe out,?_,?_,?_⟩
  · unfold FIp_SemanticArithmetic.mul
    rw [call]
    rfl
  · simpa only [Canon,to_from] using hc
  · exact hv
#print axioms mul
end AspisR1.JGb_MainTotal
end
