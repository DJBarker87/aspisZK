import AspisV8R19.R591CompleteBlockExecution
import AspisV8R19.R582SequentialTapeExecution

set_option autoImplicit false
namespace AspisV8R19.R592FiniteBlockExecution
open MemoizedProgramLaw IndependentMeanFixedTape OracleResampling
open R591CompleteBlockExecution R589IndexedReplyExecution R587BlockSamplerBound
open R584IndependentBlockSampler R579FourBlockTape R582SequentialTapeExecution
open R580SourceWordStream R572SequentialWordMass R578FiniteWordTape
open R445InitialBlockRejectionLaw R442RejectionAlphabet SourceDuplexStep
noncomputable section

def extendBlocks (blocks : Blocks) (n : Nat) : State :=
  if h : n < 4 then blocks ⟨n,h⟩ else default

theorem extendBlocks_agree (blocks : Blocks) (i : Fin 4) :
    extendBlocks blocks i.val = blocks i := by
  simp only [extendBlocks, dif_pos i.isLt]

theorem blockTape_agree (blocks : Blocks) (i : Fin 32) :
    blockTape blocks i = blockAnswer (extendBlocks blocks) i.val := by
  apply (alphabetEquiv modulus).symm.injective
  apply Fin.ext
  rw [blockTape_value, block_mask]
  simp only [extendBlocks, dif_pos (show i.val / 8 < 4 by omega)]
  rfl

theorem block_word_tape (blocks : Blocks) :
    runTape 32 (limbs 8 4 0) (blockTape blocks) =
      some (eval (blockAnswer (extendBlocks blocks)) (limbs 8 4 0)) := by
  apply runTape_eval 32 0 _ (limbs_sequential 8 4 0) (limbs_bounded 8 4 0)
  intro i
  simpa only [Nat.zero_add] using blockTape_agree blocks i

theorem block_tape_result (blocks : Blocks) :
    (evalTape challengeBlockProgram_within_four blocks).2.1 =
      (resultEval (blockAnswer (extendBlocks blocks)) (limbs 8 4 0)).1.map
        (List.map Fin.val) := by
  have hv := evalTape_runIndexed challengeBlockProgram 4
    challengeBlockProgram_within_four blocks (extendBlocks blocks) 0
    (fun i => by simpa only [Nat.zero_add] using (extendBlocks_agree blocks i).symm)
  have hr := challengeBlock_indexed (extendBlocks blocks)
  have hout := congrArg (fun v => v.2.1) hv
  change _ = (indexedResult (extendBlocks blocks) challengeBlockProgram 0).1.1 at hout
  rw [hr] at hout
  exact hout

theorem independent_block_result_law (observe : Option (List Nat) → ℚ) :
    outputMean challengeBlockProgram observe =
      mean (fun blocks : Blocks =>
        observe ((resultEval (blockAnswer (extendBlocks blocks)) (limbs 8 4 0)).1.map
          (List.map Fin.val))) := by
  rw [outputMean, ← mean_evalTape_eq_independentMean challengeBlockProgram 4
    challengeBlockProgram_within_four (fun v => observe v.2.1)]
  apply mean_congr
  intro blocks
  rw [block_tape_result]

#print axioms extendBlocks_agree
#print axioms blockTape_agree
#print axioms block_word_tape
#print axioms block_tape_result
#print axioms independent_block_result_law
end
end AspisV8R19.R592FiniteBlockExecution
