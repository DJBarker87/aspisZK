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

private def limbBlock_within_rollover (budget : Nat) (c : BlockCursor) :
    Within (limbBlockProgram budget c) (rolloverCount budget c.index) := by
  induction budget generalizing c with
  | zero => exact Within.done _ _
  | succ budget ih =>
      by_cases hi : c.index.val = 8
      · simp only [limbBlockProgram, readBlockProgram, hi, ↓reduceDIte,
          OracleProgramOps.bind]
        have h : Within (Program.ask () (fun block =>
            if masked 31 (word block 0) = 2147483647 then limbBlockProgram budget ⟨block,1⟩
            else .done (some (masked 31 (word block 0)),⟨block,1⟩)))
            (rolloverCount budget ⟨1, by decide⟩ + 1) := by
          apply Within.ask () _ (rolloverCount budget ⟨1, by decide⟩)
          intro block
          by_cases hr : masked 31 (word block 0) = 2147483647
          · simp only [if_pos hr]
            exact ih ⟨block,1⟩
          · simp only [if_neg hr]
            exact Within.done _ _
        simpa [rolloverCount, hi, Nat.add_comm] using h
      · simp only [limbBlockProgram, readBlockProgram, hi, ↓reduceDIte,
          OracleProgramOps.bind]
        by_cases hr : masked 31 (word c.block ⟨c.index.val, by omega⟩) = 2147483647
        · simp only [if_pos hr]
          simpa [rolloverCount, hi] using ih ⟨c.block,⟨c.index.val+1,by omega⟩⟩
        · simp only [if_neg hr]
          exact Within.done _ _

private def limbBlock_eight_within_one (c : BlockCursor) :
    Within (limbBlockProgram 8 c) 1 := by
  have h := limbBlock_within_rollover 8 c
  have hle := rolloverCount_eight_le_one
    (⟨c.block,c.block,c.index⟩ : QM31SamplerProgram.Cursor)
  change rolloverCount 8 c.index ≤ 1 at hle
  have heq : rolloverCount 8 c.index + (1 - rolloverCount 8 c.index) = 1 := by omega
  rw [← heq]
  exact pad h _

private def limbBlock_initial_within_zero (b : State) :
    Within (limbBlockProgram 8 ⟨b,0⟩) 0 := by
  simpa [rolloverCount] using limbBlock_within_rollover 8 ⟨b,0⟩

private def limbsBlock_within (count : Nat) (c : BlockCursor) :
    Within (limbsBlockProgram count c) count := by
  induction count generalizing c with
  | zero => exact Within.done _ _
  | succ count ih =>
      simp only [limbsBlockProgram]
      have h : Within (OracleProgramOps.bind (limbBlockProgram 8 c) (fun r => match r.1 with
          | none => .done (none,r.2)
          | some a => bind (limbsBlockProgram count r.2) (fun tail =>
              .done (tail.1.map (a::·),tail.2)))) (1 + count) := by
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
      rw [Nat.add_comm] at h
      exact h

private def limbsBlock_initial_within_three (b : State) :
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

def challengeBlockProgram_within_four :
    Within challengeBlockProgram 4 := by
  unfold challengeBlockProgram
  exact Within.ask () _ 3 (fun block => limbsBlock_initial_within_three block)

#print axioms challengeBlockProgram_within_four
end AspisV8R19.R587BlockSamplerBound
