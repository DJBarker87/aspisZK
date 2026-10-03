import AspisV8R19.R444InitialSourceLimb

set_option autoImplicit false
namespace AspisV8R19.R452NoRefillProgram

open AspisV8R19.QM31SamplerProgram
open AspisV8R19.SamplerWords
open AspisV8R19.OracleProgramOps
open AspisV8R19.SourceOraclePrograms

/-- Within the available suffix of the current block, the source-shaped
program terminates with the same result as the run model and never refills. -/
theorem limbProgram_no_refill (H : Bytes → State) (n : Nat) (c : Cursor)
    (h : c.index.val + n ≤ 8) :
    limbProgram n c =
      Program.done ((limbRun H n c).2) := by
  induction n generalizing c with
  | zero =>
      simp [limbProgram, limbRun]
  | succ n ih =>
      have hlt : c.index.val < 8 := by omega
      have hneq : c.index.val ≠ 8 := by omega
      let i : Fin 8 := ⟨c.index.val, hlt⟩
      let c' : Cursor :=
        ⟨c.state, c.block, ⟨c.index.val + 1, by omega⟩⟩
      have hp : readProgram c = .done (word c.block i, c') := by
        simp [readProgram, hneq, i, c']
      have hr : readRun H c = ([], (word c.block i, c')) := by
        simp [readRun, hneq, i, c']
      simp only [limbProgram, hp, bind, limbRun, hr]
      by_cases hs : masked 31 (word c.block i) = 2147483647
      · simp only [if_pos hs]
        have hc' : c'.index.val + n ≤ 8 := by
          change c.index.val + 1 + n ≤ 8
          omega
        exact ih c' hc'
      · simp [hs]

#print axioms limbProgram_no_refill

end AspisV8R19.R452NoRefillProgram
