import AspisV8R19.Q22SamplerProgram
import AspisV8R19.SamplerProgramQueryBound

set_option autoImplicit false
namespace AspisV8R19.R466Q22TraceBound
open AspisV8R19.Q22SamplerProgram
open AspisV8R19.SourceDuplexStep
open AspisV8R19.SamplerProgramQueryBound
open AspisV8R19.Q22WordScan
open AspisV8R19.SourceDuplexStep
open AspisV8R19.SamplerWords
open AspisV8R19.DuplexFrames

theorem calls_length_two (H : Bytes → State) (s : State) :
    (calls H s).length = 2 := by
  simp [calls, SourceDuplexStep.calls]

theorem loopRun_trace_length_le (H : Bytes → State) :
    ∀ (n : Nat) (s : State) (q : ScanState),
      (loopRun H n s q).1.length ≤ 2 * n := by
  intro n
  induction n with
  | zero => intro s q; rfl
  | succ n ih =>
      intro s q
      unfold loopRun
      by_cases hd : q.draws < 64
      · rw [if_pos hd]
        let p := step H s
        let r := scan q (words 18 p.1)
        by_cases hs : r.2 = true
        · simp [p, r, hs]
          have hc := calls_length_two H s
          omega
        · simp only [p, r, hs, Bool.false_eq_true, ↓reduceIte, List.length_append]
          have hi :
              (loopRun H n (step H s).2
                (scan q (words 18 (step H s).1)).1).1.length ≤ 2 * n := by
            simpa [p, r] using ih p.2 r.1
          have hc := calls_length_two H s
          omega
      · simp [hd]

theorem challengeRun_trace_length_le (H : Bytes → State) (s : State) :
    (challengeRun H s).1.length ≤ 16 := by
  simpa [challengeRun] using loopRun_trace_length_le H 8 s ⟨[], 0⟩

theorem challengeProgram_within_16 (s : State) :
    Within 16 (challengeProgram s) := by
  intro H
  rw [challenge_exact]
  exact challengeRun_trace_length_le H s

#print axioms calls_length_two
#print axioms loopRun_trace_length_le
#print axioms challengeRun_trace_length_le
#print axioms challengeProgram_within_16
end AspisV8R19.R466Q22TraceBound
