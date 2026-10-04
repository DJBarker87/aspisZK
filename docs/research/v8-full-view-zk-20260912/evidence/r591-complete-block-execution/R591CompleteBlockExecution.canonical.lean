import AspisV8R19.R589IndexedReplyExecution
import AspisV8R19.R587BlockSamplerBound

set_option autoImplicit false
namespace AspisV8R19.R591CompleteBlockExecution
open MemoizedProgramLaw OracleProgramOps IndependentMeanFixedTape
open R584IndependentBlockSampler R589IndexedReplyExecution R580SourceWordStream
open R572SequentialWordMass R445InitialBlockRejectionLaw SourceDuplexStep

def limbsBlockBudget (budget : Nat) : Nat → BlockCursor →
    Program Unit State (Option (List Nat) × BlockCursor)
  | 0,c => .done (some [],c)
  | count+1,c => bind (limbBlockProgram budget c) (fun first => match first.1 with
      | none => .done (none,first.2)
      | some a => bind (limbsBlockBudget budget count first.2) (fun tail =>
          .done (tail.1.map (a::·),tail.2)))

theorem limbsBlockBudget_eight (count : Nat) (c : BlockCursor) :
    limbsBlockProgram count c = limbsBlockBudget 8 count c := by
  induction count generalizing c with
  | zero => rfl
  | succ count ih =>
      simp only [limbsBlockProgram,limbsBlockBudget]
      congr 1
      funext first
      cases first.1 with
      | none => rfl
      | some a => rw [ih]

theorem limbsBlockBudget_indexed (answer : Nat → State) (budget count n : Nat) :
    indexedResult answer (limbsBlockBudget budget count (blockCursorAt answer n)) (nextBlock n) =
      let r := resultEval (blockAnswer answer) (limbs budget count n)
      ((r.1.map (List.map Fin.val),blockCursorAt answer r.2),nextBlock r.2) := by
  induction count generalizing n with
  | zero => rfl
  | succ count ih =>
      rw [resultEval_limbs_succ]
      simp only [limbsBlockBudget,indexedResult_bind,limbBlock_indexed]
      cases hs : resultEval (blockAnswer answer) (scan budget n) with
      | mk head next =>
          cases head with
          | none => simp only [Option.map_none,indexedResult_done]
          | some a =>
              simp only [Option.map_some,indexedResult_bind,ih]
              cases ht : resultEval (blockAnswer answer) (limbs budget count next) with
              | mk tail stop =>
                  cases tail with
                  | none => simp only [prependResult,Option.map_none,indexedResult_done]
                  | some xs => simp only [prependResult,Option.map_some,List.map_cons,indexedResult_done]

theorem limbsBlock_indexed (answer : Nat → State) (count n : Nat) :
    indexedResult answer (limbsBlockProgram count (blockCursorAt answer n)) (nextBlock n) =
      let r := resultEval (blockAnswer answer) (limbs 8 count n)
      ((r.1.map (List.map Fin.val),blockCursorAt answer r.2),nextBlock r.2) := by
  rw [limbsBlockBudget_eight]
  exact limbsBlockBudget_indexed answer 8 count n

theorem challengeBlock_indexed (answer : Nat → State) :
    indexedResult answer challengeBlockProgram 0 =
      let r := resultEval (blockAnswer answer) (limbs 8 4 0)
      ((r.1.map (List.map Fin.val),blockCursorAt answer r.2),nextBlock r.2) := by
  change indexedResult answer (limbsBlockProgram 4 ⟨answer 0,0⟩) 1 = _
  change indexedResult answer (limbsBlockProgram 4 (blockCursorAt answer 0)) (nextBlock 0) = _
  exact limbsBlock_indexed answer 4 0

#print axioms limbsBlockBudget_eight
#print axioms limbsBlockBudget_indexed
#print axioms limbsBlock_indexed
#print axioms challengeBlock_indexed
end AspisV8R19.R591CompleteBlockExecution
