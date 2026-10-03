import AspisV8R19.QM31SamplerProgram

set_option autoImplicit false
namespace R444InitialSourceLimb
open AspisV8R19.QM31SamplerProgram
open AspisV8R19.SamplerWords
abbrev State := AspisV8R19.SourceDuplexStep.State
abbrev Bytes := AspisV8R19.DuplexFrames.Bytes

/-- Scan a finite sequence of already-read words using the source sentinel. -/
def sourceScan : List Nat → Option Nat × Nat
  | [] => (none, 0)
  | w :: ws =>
      if masked 31 w = 2147483647 then
        let tail := sourceScan ws
        (tail.1, tail.2 + 1)
      else (some (masked 31 w), 1)

theorem limbRun_no_refill (H : Bytes → State) (n : Nat) (c : Cursor)
    (h : c.index.val + n ≤ 8) :
    (limbRun H n c).1 = [] ∧
    (limbRun H n c).2.2.state = c.state ∧
    (limbRun H n c).2.2.block = c.block ∧
    (limbRun H n c).2.2.index.val ≤ 8 := by
  induction n generalizing c with
  | zero =>
      simp only [limbRun]
      exact ⟨rfl, rfl, rfl, Nat.le_of_lt_succ c.index.isLt⟩
  | succ n ih =>
      have hlt : c.index.val < 8 := by omega
      have hneq : c.index.val ≠ 8 := by omega
      let i : Fin 8 := ⟨c.index.val, hlt⟩
      let c' : Cursor := ⟨c.state, c.block, ⟨c.index.val + 1, by omega⟩⟩
      have hr : readRun H c = ([], (word c.block i, c')) := by
        simp [readRun, hneq, i, c']
      simp only [limbRun, hr]
      by_cases hs : masked 31 (word c.block i) = 2147483647
      · simp only [hs]
        have hcidx : c.index.val + 1 + n ≤ 8 := by omega
        have hc' : c'.index.val + n ≤ 8 := by
          change c.index.val + 1 + n ≤ 8
          exact hcidx
        obtain ⟨hcall, hs', hb, hi⟩ := ih c' hc'
        exact ⟨hcall, hs', hb, hi⟩
      · simp only [hs]
        refine ⟨rfl, rfl, rfl, ?_⟩
        dsimp [c']
        simp
        omega

#print axioms limbRun_no_refill
end R444InitialSourceLimb
