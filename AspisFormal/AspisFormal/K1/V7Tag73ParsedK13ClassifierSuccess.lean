import AspisFormal.K1.V7Tag73ParsedK13K14Classifier

/-! # Parser-level K1.3 classifier success -/

set_option autoImplicit false

namespace AspisK1.V7Tag73ParsedK13ClassifierSuccess

open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A parser-level certificate forces the total parser classifier to return
a success certificate on those exact words and proof bytes. -/
theorem classify_parsed_k13_succeeds_of_certificate
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {proof : Tag73K12ParsedProof}
    (certificate : ParsedK13Certificate decoder words proof) :
    ∃ returned : ParsedK13Certificate decoder words proof,
      classifyParsedK13 decoder words proof = .inl returned := by
  cases classifierExact : classifyParsedK13 decoder words proof with
  | inl returned => exact ⟨returned, rfl⟩
  | inr error =>
      cases error with
      | idealRejected rejected => exact (rejected certificate.accepts).elim
      | queryPhaseFailure failure =>
          exact (certificate.noQueryFailure failure).elim
      | oneFoldReductionFailure failure =>
          exact (certificate.noFoldFailure failure).elim
      | initialListCapFailure failure =>
          exact (certificate.noListCapFailure failure).elim

#print axioms classify_parsed_k13_succeeds_of_certificate

end
end AspisK1.V7Tag73ParsedK13ClassifierSuccess
