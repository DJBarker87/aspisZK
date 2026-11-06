import PCC_SingleOutputReference
set_option autoImplicit false
namespace PCC
open PCA
/-- Symbolic zero-cell reduction for single-output witnesses. Eight fixed
zero limbs only; no large recurrence and no native field multiplication. -/
theorem validate_single (commitment : Digest) :
    validatePair (singleWitness commitment) =
      if canonical commitment then .ok () else .error .NonCanonicalCommitment := by
  have hz : canonical (Vector.replicate 8 0) = true := by simp [canonical]
  by_cases hc : canonical commitment = true <;>
    simp [validatePair,singleWitness,fieldMul,fieldSub,hz,hc]

theorem single_on_canonical (commitment : Digest) (s : PCA_State)
    (h : canonical commitment = true) :
    (singleOutputReference commitment s).reply = .ok (singleWitness commitment) := by
  simp only [singleOutputReference, validate_single,h,↓reduceIte]
#print axioms validate_single
#print axioms single_on_canonical
end PCC
