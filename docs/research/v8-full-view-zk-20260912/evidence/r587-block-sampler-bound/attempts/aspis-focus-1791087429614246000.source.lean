import AspisV8R19.R584IndependentBlockSampler
import AspisV8R19.IndependentMeanFixedTapeQM31
import AspisV8R19.SamplerCursorTightBound

set_option autoImplicit false
namespace AspisV8R19.R587BlockSamplerBound
open MemoizedProgramLaw OracleProgramOps SamplerWords
open QM31SamplerProgram SamplerCursorTightBound
open R584IndependentBlockSampler
open IndependentMeanFixedTape IndependentMeanFixedTapeQM31

abbrev State := SourceDuplexStep.State

private def mirror (c : BlockCursor) : Cursor := ⟨default,c.block,c.index⟩

private theorem limbBlock_within_rollover (budget : Nat) (c : BlockCursor) :
    Within (limbBlockProgram budget c) (rolloverCount budget c.index) := by
  induction budget generalizing c with
  | zero => exact Within.done _ _
  | succ budget ih =>
      by_cases hi : c.index.val = 8
      · simp only [limbBlockProgram, readBlockProgram, hi, ↓reduceDIte]
        apply withinBind 1 (rolloverCount budget ⟨1, by decide⟩)
        · exact Within.ask () _ _ (fun block => Within.done _ _)
        · intro r
          by_cases hr : masked 31 r.1 = 2147483647
          · simpa [hr] using ih r.2
          · exact Within.done _ _
      · simp only [limbBlockProgram, readBlockProgram, hi, ↓reduceDIte]
        apply withinBind 0 (rolloverCount budget ⟨c.index.val + 1, by omega⟩)
        · exact Within.done _ _
        · intro r
          by_cases hr : masked 31 r.1 = 2147483647
          · simpa [hr] using ih r.2
          · exact Within.done _ _

private theorem limbBlock_eight_within_one (c : BlockCursor) :
    Within (limbBlockProgram 8 c) 1 := by
  have h := limbBlock_within_rollover 8 c
  have hle := rolloverCount_eight_le_one (mirror c)
  exact pad h (1 - rolloverCount 8 c.index)

private theorem limbBlock_initial_within_zero (b : State) :
    Within (limbBlockProgram 8 ⟨b,0⟩) 0 := by
  simpa [rolloverCount] using limbBlock_within_rollover 8 ⟨b,0⟩

private theorem limbsBlock_within (count : Nat) (c : BlockCursor) :
    Within (limbsBlockProgram count c) count := by
  induction count generalizing c with
  | zero => exact Within.done _ _
  | succ count ih =>
      simp only [limbsBlockProgram]
      apply withinBind 1 count (limbBlockProgram 8 c)
      · exact limbBlock_eight_within_one c
      · intro r
        cases r.1 with
        | none => exact Within.done _ _
        | some a =>
            apply withinBind count 0 (limbsBlockProgram count r.2)
            · exact ih r.2
            · intro tail
              exact Within.done _ _

private theorem limbsBlock_initial_within_three (b : State) :
    Within (limbsBlockProgram 4 ⟨b,0⟩) 3 := by
  simp only [limbsBlockProgram]
  apply withinBind 0 3 (limbBlockProgram 8 ⟨b,0⟩)
  · exact limbBlock_initial_within_zero b
  · intro r
    cases r.1 with
    | none => exact Within.done _ _
    | some a =>
        apply withinBind 3 0 (limbsBlockProgram 3 r.2)
        · exact limbsBlock_within 3 r.2
        · intro tail
          exact Within.done _ _

theorem challengeBlockProgram_within_four :
    Within challengeBlockProgram 4 := by
  unfold challengeBlockProgram
  exact Within.ask () _ 3 (fun block => limbsBlock_initial_within_three block)

#print axioms challengeBlockProgram_within_four
end AspisV8R19.R587BlockSamplerBound
