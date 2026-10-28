import R1Z.ProverCommitCursor
import R1Z.ProverCommitSourceCallerLaw

set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSourceDecoder
open R1Z.ProverCommitTapeCompletion R1Z.ProverCommitSequentialFibres
  R1Z.ProverCommitCursor R1Z.CommitReadsR1 R1Z.FinalR1PBin
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
attribute [local irreducible] L₁ L₂ E₁ E₂ arrayCarrierEquiv

/-- Exact failure classification on the existing block-answer carriers. -/
theorem quotient_exhausted (e : Inputs) : quotientDecoder (K := K) e = none ↔
    Exhausted (wordsE E₁ e.1) L₁ ∨ Exhausted (wordsE E₂ e.2) L₂ := by
  rw [quotient_failure]
  have h₁ := decoder_exhausted (K := K) ((inputEquiv e).1) L₁ (by
    unfold E₁; omega)
  have h₂ := decoder_exhausted (K := K) ((inputEquiv e).2) L₂ (by
    unfold E₂; omega)
  exact or_congr h₁ h₂

/-- The sole source premise here is the same caller equation needed for
the quotient fibre law; no separate failure/cursor premise is necessary. -/
theorem caller_exhausted (decode : Inputs → Option (R0Z.JointView.Tape K
    (R1Z.ProverCommitWordCarrier.sourceBase (K := K))))
    (caller : ∀ e, quotientDecode decode e = quotientDecoder e) (e : Inputs) :
    decode e = none ↔
      Exhausted (wordsE E₁ e.1) L₁ ∨ Exhausted (wordsE E₂ e.2) L₂ := by
  have hnone : decode e = none ↔ quotientDecode decode e = none := by
    cases hd : decode e <;> simp [quotientDecode, hd]
  rw [hnone, caller e]
  exact quotient_exhausted e

#print axioms quotient_exhausted
#print axioms caller_exhausted
end R1Z.ProverCommitSourceDecoder
