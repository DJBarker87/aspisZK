import RPu_FIp_MaskValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_MaskDecode
/-- Scalar decoder identity, without unfolding any populated coefficient array. -/
theorem value (x : FIp_SemanticArithmetic.PQ) :
    FIp_SemanticValues.decode (FIp_SemanticArithmetic.fromProbe x)=ExtractedMaskQM31Exact.decode x := by
  rw [FIp_SemanticValues.decode,FIp_SemanticValues.to_from]
#print axioms value
end AspisR1.FJn_MaskDecode
end
