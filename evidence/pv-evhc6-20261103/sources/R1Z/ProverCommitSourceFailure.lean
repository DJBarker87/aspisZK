import R1Z.ProverCommitSourceCounts

/-! Decoder/packing cannot add failure. Exhaustion identification with the
shipped caller's cursor remains a source execution obligation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSourceDecoder
open R1Z.ProverCommitSequentialFibres R1Z.ProverCommitWordCarrier
attribute [local instance] Classical.propDecidable
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
attribute [local irreducible] L₁ L₂ E₁ E₂ arrayCarrierEquiv sourceBase

theorem quotient_failure (e : Inputs) : quotientDecoder (K := K) e = none ↔
    arrayDecode (accepted (K := K)) (E₁*8) L₁ 16 (inputEquiv e).1 = none ∨
    arrayDecode (accepted (K := K)) (E₂*8) L₂ 16 (inputEquiv e).2 = none := by
  cases h₁ : arrayDecode (accepted (K := K)) (E₁*8) L₁ 16 (inputEquiv e).1 <;>
    cases h₂ : arrayDecode (accepted (K := K)) (E₂*8) L₂ 16 (inputEquiv e).2 <;>
      simp [quotientDecoder, pairDecode, h₁, h₂]

#print axioms quotient_failure
end R1Z.ProverCommitSourceDecoder
