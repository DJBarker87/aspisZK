import RPz7_FIp_SemanticArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_SemanticValues
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic
abbrev Canon (x : MQ) := ExtractedMaskQM31Exact.CurrentCanonicalQM (toProbe x)
abbrev decode (x : MQ) := ExtractedMaskQM31Exact.decode (toProbe x)

theorem to_from (x : PQ) : toProbe (fromProbe x)=x := rfl

theorem add (x y z : MQ) (hx : Canon x) (hy : Canon y)
    (run : FIp_SemanticArithmetic.add x y=ok z) : Canon z ∧ decode z=decode x+decode y := by
  obtain ⟨native,hn,hc,hv⟩ := ExtractedMaskQM31Exact.current_qm_add_exact (toProbe x) (toProbe y) hx hy
  unfold FIp_SemanticArithmetic.add at run
  rw [hn] at run
  have same : fromProbe native=z := Result.ok.inj run
  subst z
  exact ⟨by simpa only [Canon,to_from] using hc,by simpa only [decode,to_from] using hv⟩

theorem mul (x y z : MQ) (hx : Canon x) (hy : Canon y)
    (run : FIp_SemanticArithmetic.mul x y=ok z) : Canon z ∧ decode z=decode x*decode y := by
  obtain ⟨native,hn,hc,hv⟩ := ExtractedMaskQM31Exact.current_qm_mul_exact (toProbe x) (toProbe y) hx hy
  unfold FIp_SemanticArithmetic.mul at run
  rw [hn] at run
  have same : fromProbe native=z := Result.ok.inj run
  subst z
  exact ⟨by simpa only [Canon,to_from] using hc,by simpa only [decode,to_from] using hv⟩

#print axioms to_from
#print axioms add
#print axioms mul
end AspisR1.FIp_SemanticValues
end
