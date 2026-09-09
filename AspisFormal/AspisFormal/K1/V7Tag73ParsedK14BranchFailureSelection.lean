import AspisFormal.K1.V7Tag73K14FamilyFailureMembership
import AspisFormal.K1.V7Tag73ParsedK13K14Classifier

/-! # Parser-level K1.4 branch/failure selection equality -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

namespace AspisK1.V7Tag73ParsedK14BranchFailureSelection

open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A replay branch and width-29 failure which refer to the same parser data
select the same canonical candidate pair. -/
theorem parsed_branch_selected_eq_choose_width29_failure
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {proof : Tag73K12ParsedProof}
    {gamma : QM31Exact}
    (branch : RestoredSelectedBranch decoder words gamma)
    (gammaExact : proof.gamma = gamma)
    (finalExact : branch.disclosedFinal = proof.disclosedFinal)
    (scheduleExact : branch.schedule = proof.schedule)
    (failure : Width29DecompositionFailure decoder words proof.gamma
      proof.disclosedFinal proof.schedule) :
    branch.selected = Classical.choose failure := by
  subst gamma
  have branchSelectedOnProof := branch.selectedExact
  rw [finalExact, scheduleExact] at branchSelectedOnProof
  have failureSelectedOnProof := (Classical.choose_spec failure).1
  apply Option.some.inj
  exact branchSelectedOnProof.symm.trans failureSelectedOnProof

#print axioms parsed_branch_selected_eq_choose_width29_failure

end
end AspisK1.V7Tag73ParsedK14BranchFailureSelection
