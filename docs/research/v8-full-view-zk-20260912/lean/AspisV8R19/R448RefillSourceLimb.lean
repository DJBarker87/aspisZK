import AspisV8R19.R444InitialSourceLimb

set_option autoImplicit false
namespace AspisV8R19.R448RefillSourceLimb
open AspisV8R19.QM31SamplerProgram
open AspisV8R19.SourceDuplexStep
open AspisV8R19.SamplerWords
open AspisV8R19.R444InitialSourceLimb

abbrev State := AspisV8R19.SourceDuplexStep.State
abbrev Bytes := AspisV8R19.DuplexFrames.Bytes

theorem limbRun_refill_scanAt (H : Bytes → State) (n : Nat) (c : Cursor)
    (hc : c.index.val = 8) (hbudget : n + 1 ≤ 8) :
    (limbRun H (n + 1) c).1 = calls H c.state ∧
    (limbRun H (n + 1) c).2.1 =
      (scanAt (step H c.state).1 0 (n + 1) (by omega)).1 ∧
    (limbRun H (n + 1) c).2.2.state = (step H c.state).2 ∧
    (limbRun H (n + 1) c).2.2.block = (step H c.state).1 ∧
    (limbRun H (n + 1) c).2.2.index.val =
      (scanAt (step H c.state).1 0 (n + 1) (by omega)).2 := by
  let p := step H c.state
  let c' : Cursor := ⟨p.2, p.1, 1⟩
  have htail : c'.index.val + n ≤ 8 := by dsimp [c']; omega
  have hr : readRun H c = (calls H c.state, (word p.1 0, c')) := by
    simp [readRun, hc, p, c']
  have hword : word p.1 0 = word p.1 ⟨0, by omega⟩ := rfl
  have hsuffix : blockSuffix p.1 0 (n + 1) (by omega) =
      masked 31 (word p.1 0) :: blockSuffix p.1 1 n (by omega) := by
    simp [blockSuffix, hword]
  simp only [limbRun, hr]
  by_cases hs : masked 31 (word p.1 0) = 2147483647
  · simp only [if_pos hs]
    have htailRun := limbRun_scanAt H n c' htail
    rcases htailRun with ⟨hcall, hvalue, hstate, hblock, hindex⟩
    simp [scanAt, hsuffix, sourceScan, hs, hcall, hvalue, hstate, hblock, hindex, c', p]
    omega
  · simp [scanAt, hsuffix, sourceScan, hs, c', p]

#print axioms limbRun_refill_scanAt
end AspisV8R19.R448RefillSourceLimb
