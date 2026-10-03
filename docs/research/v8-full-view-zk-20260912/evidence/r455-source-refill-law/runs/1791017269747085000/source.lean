import AspisV8R19.R452NoRefillProgram

set_option autoImplicit false
namespace AspisV8R19.R454RefillProgramShape

open AspisV8R19.QM31SamplerProgram
open AspisV8R19.SamplerWords
open AspisV8R19.SourceOraclePrograms
open AspisV8R19.MemoizedProgramLaw

abbrev State := AspisV8R19.SourceDuplexStep.State
abbrev Bytes := AspisV8R19.DuplexFrames.Bytes

/-- At the block sentinel, the source program asks for a fresh duplex block
and returns the result modeled by the run starting at that new block. -/
theorem limbProgram_refill_shape (c : Cursor) (n : Nat)
    (hc : c.index.val = 8) (hn : n + 1 ≤ 8) :
    limbProgram (n + 1) c =
      AspisV8R19.OracleProgramOps.bind (squeezeProgram c.state) (fun p =>
        Program.done
          ((limbRun (fun _ => p.2) (n + 1) ⟨p.2, p.1, 0⟩).2)) := by
  have htail (p : State × State) :
      limbProgram n ⟨p.2, p.1, 1⟩ =
        Program.done ((limbRun (fun _ => p.2) n ⟨p.2, p.1, 1⟩).2) := by
    apply AspisV8R19.R452NoRefillProgram.limbProgram_no_refill
    change 1 + n ≤ 8
    omega
  have hp : readProgram c =
      AspisV8R19.OracleProgramOps.bind (squeezeProgram c.state) (fun p =>
        Program.done (word p.1 0, ⟨p.2, p.1, 1⟩)) := by
    simp [readProgram, hc]
  have hrun (p : State × State) :
      (limbRun (fun _ => p.2) (n + 1) ⟨p.2, p.1, 0⟩).2 =
        if masked 31 (word p.1 0) = 2147483647 then
      (limbRun (fun _ => p.2) n ⟨p.2, p.1, 1⟩).2
        else (some (masked 31 (word p.1 0)), ⟨p.2, p.1, 1⟩) := by
    by_cases hs : masked 31 (word p.1 0) = 2147483647
    · simp [limbRun, readRun, hs]
    · simp [limbRun, readRun, hs]
  rw [limbProgram, hp]
  simp only [SourceOraclePrograms.squeezeProgram, AspisV8R19.OracleProgramOps.bind]
  congr 1
  funext out next
  by_cases hs : masked 31 (word out 0) = 2147483647
  · simp only [if_pos hs]
    exact htail (next, out)
  · simp [hs, hrun (out, next)]

#print axioms limbProgram_refill_shape

end AspisV8R19.R454RefillProgramShape
