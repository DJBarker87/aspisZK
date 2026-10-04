import AspisV8R19.R592FiniteBlockExecution
import AspisV8R19.R593DecodedTupleObservation

set_option autoImplicit false
namespace AspisV8R19.R594JointChallengeMass
open MemoizedProgramLaw OracleResampling IndependentMeanFixedTape
open R592FiniteBlockExecution R593DecodedTupleObservation R584IndependentBlockSampler
open R579FourBlockTape R580SourceWordStream R572SequentialWordMass R578FiniteWordTape
open R445InitialBlockRejectionLaw SourceDuplexStep QM31SamplerProgram
noncomputable section

def tupleEvent (target : Fin 4 → Fin modulus) (out : Option (List Nat)) : ℚ :=
  if out = some ((List.ofFn target).map Fin.val) then 1 else 0

theorem block_tuple_mass (target : Fin 4 → Fin modulus) :
    outputMean challengeBlockProgram (fun r => tupleEvent target r.1) =
      ((1-(1/(2147483648 : ℚ))^8)/2147483647)^4 := by
  rw [independent_block_result_law]
  calc
    mean (fun blocks : Blocks => tupleEvent target
      ((resultEval (blockAnswer (extendBlocks blocks)) (limbs 8 4 0)).1.map
        (List.map Fin.val))) =
      mean (fun blocks : Blocks => observeTape (observedList (List.ofFn target))
        (runTape 32 (limbs 8 4 0) (blockTape blocks))) := by
          apply mean_congr
          intro blocks
          rw [block_word_tape]
          simp only [observeTape]
          rw [← eval_result]
          exact decoded_tuple_observation (List.ofFn target) _
    _ = _ := four_block_tuple_mass target 0

theorem source_independent_tuple_mass (s : SourceDuplexStep.State)
    (target : Fin 4 → Fin modulus) :
    outputMean (challengeProgram s) (fun r => tupleEvent target r.1) =
      ((1-(1/(2147483648 : ℚ))^8)/2147483647)^4 := by
  rw [challenge_independent_block]
  exact block_tuple_mass target

#print axioms block_tuple_mass
#print axioms source_independent_tuple_mass
end
end AspisV8R19.R594JointChallengeMass
