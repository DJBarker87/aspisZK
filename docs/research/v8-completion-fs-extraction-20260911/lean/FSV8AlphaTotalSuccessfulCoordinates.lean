import FSV8AlphaCompleteCoordinateRouter

/-!
# Successful complete alpha coordinates

The V8 alpha router exposes four output blocks and four duplex-advance
digests.  Success depends only on the output blocks: under the existing
four-block/raw-stream equivalence they must form a successful Tag-73 ordinary
sample.  This leaf packages that observation as the exact successful-subtype
equivalence required by the existing complete causal ordinary probability
theorem.

Advance digests are retained verbatim.  No freshness, source coverage,
probability, or accepted-execution premise occurs here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
set_option maxRecDepth 1200

namespace AspisV8Completion.FSV8AlphaTotalSuccessfulCoordinates

open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73VariablePrefixGammaFactorization

noncomputable section

/-- The complete routed alpha tape succeeds exactly when its four output
blocks decode successfully.  The four advance digests are causal nuisance
coordinates and do not affect decoder success. -/
def relationAlphaTotalSucceeds (sample : RelationAlphaTotalTape) : Prop :=
  Tag73RawSucceeds (fourGammaBlocksRawEquiv sample.1)

instance (sample : RelationAlphaTotalTape) :
    Decidable (relationAlphaTotalSucceeds sample) := by
  unfold relationAlphaTotalSucceeds
  infer_instance

/-- A successful routed V8 alpha tape is exactly one successful Tag-73 raw
stream paired with the same four advance digests. -/
def successfulRelationAlphaTotalEquiv :
    {sample : RelationAlphaTotalTape // relationAlphaTotalSucceeds sample} ≃
      SuccessfulTag73DuplexOrdinaryAttempt where
  toFun sample :=
    (⟨fourGammaBlocksRawEquiv sample.1.1, sample.2⟩, sample.1.2)
  invFun sample :=
    ⟨(fourGammaBlocksRawEquiv.symm sample.1.1, sample.2), by
      unfold relationAlphaTotalSucceeds
      rw [fourGammaBlocksRawEquiv.apply_symm_apply]
      exact sample.1.2⟩
  left_inv sample := by
    apply Subtype.ext
    apply Prod.ext
    · exact fourGammaBlocksRawEquiv.symm_apply_apply sample.1.1
    · rfl
  right_inv sample := by
    apply Prod.ext
    · apply Subtype.ext
      exact fourGammaBlocksRawEquiv.apply_symm_apply sample.1.1
    · rfl

noncomputable instance successfulRelationAlphaTotalNonempty :
    Nonempty {sample : RelationAlphaTotalTape //
      relationAlphaTotalSucceeds sample} :=
  ⟨successfulRelationAlphaTotalEquiv.symm
    (Classical.choice
      (inferInstance : Nonempty SuccessfulTag73DuplexOrdinaryAttempt))⟩

@[simp] theorem successfulRelationAlphaTotalEquiv_advance
    (sample : {sample : RelationAlphaTotalTape //
      relationAlphaTotalSucceeds sample}) :
    (successfulRelationAlphaTotalEquiv sample).2 = sample.1.2 := by
  rfl

@[simp] theorem successfulRelationAlphaTotalEquiv_raw
    (sample : {sample : RelationAlphaTotalTape //
      relationAlphaTotalSucceeds sample}) :
    (successfulRelationAlphaTotalEquiv sample).1.1 =
      fourGammaBlocksRawEquiv sample.1.1 := by
  rfl

#print axioms relationAlphaTotalSucceeds
#print axioms successfulRelationAlphaTotalEquiv
#print axioms successfulRelationAlphaTotalNonempty
#print axioms successfulRelationAlphaTotalEquiv_advance
#print axioms successfulRelationAlphaTotalEquiv_raw

end
end AspisV8Completion.FSV8AlphaTotalSuccessfulCoordinates
