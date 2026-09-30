import AspisV8R19.QM31SamplerProgram
import AspisV8R19.SamplerProgramQueryBound

/-! Symbolic rollover accounting for the source cursor.

The counter records only reads which begin at cursor index eight.  It is
independent of the accepted/rejected value and therefore preserves early
success and exhaustion branches.
-/
set_option autoImplicit false
namespace AspisV8R19.SamplerCursorTightBound

open DuplexFrames SourceDuplexStep SamplerWords
open AspisV8R19.QM31SamplerProgram
open AspisV8R19.SamplerProgramQueryBound

def rolloverCount : Nat → Fin 9 → Nat
  | 0, _ => 0
  | n+1, c =>
      if h : c.val = 8 then
        1 + rolloverCount n ⟨1, by decide⟩
      else
        rolloverCount n ⟨c.val + 1, by omega⟩

theorem limbRun_rollover_bound (H : Bytes → State) (n : Nat) (c : Cursor) :
    (limbRun H n c).1.length ≤ 2 * rolloverCount n c.index := by
  induction n generalizing c with
  | zero => simp [limbRun, rolloverCount]
  | succ n ih =>
      by_cases hi : c.index.val = 8
      · by_cases hr : masked 31 (word (step H c.state).1 0) = 2147483647
        · have ht := ih ⟨(step H c.state).2, (step H c.state).1, 1⟩
          simp [limbRun, readRun, hi, hr, rolloverCount, calls] at ht ⊢
          omega
        · simp [limbRun, readRun, hi, hr, rolloverCount, calls]
      · by_cases hr : masked 31
            (word c.block ⟨c.index.val, by omega⟩) = 2147483647
        · have ht := ih ⟨c.state, c.block, ⟨c.index.val + 1, by omega⟩⟩
          simp [limbRun, readRun, hi, hr, rolloverCount] at ht ⊢
          omega
        · simp [limbRun, readRun, hi, hr, rolloverCount]

theorem rolloverCount_eight_le_one (c : Cursor) :
    rolloverCount 8 c.index ≤ 1 := by
  cases c with
  | mk state block index =>
      fin_cases index <;> norm_num [rolloverCount]

theorem limbRun_eight_bound (H : Bytes → State) (c : Cursor) :
    (limbRun H 8 c).1.length ≤ 2 := by
  have h := limbRun_rollover_bound H 8 c
  have hc := rolloverCount_eight_le_one c
  omega

theorem limbRun_eight_initial_zero (H : Bytes → State) (c : Cursor)
    (h : c.index.val = 0) :
    (limbRun H 8 c).1.length = 0 := by
  have hb := limbRun_rollover_bound H 8 c
  have hc : rolloverCount 8 c.index = 0 := by
    simp [rolloverCount, h]
  omega

theorem limbsRun_succ_trace (H : Bytes → State) (n : Nat) (c : Cursor) :
    (limbsRun H (n + 1) c).1 =
      let r := limbRun H 8 c
      match r.2.1 with
      | none => r.1
      | some _ => r.1 ++ (limbsRun H n r.2.2).1 := by
  simp only [limbsRun]
  cases h : (limbRun H 8 c).2.1 <;> simp [h]

theorem limbsRun_tail_bound (H : Bytes → State) (n : Nat) (c : Cursor)
    (hn : n ≤ 3) :
    (limbsRun H n c).1.length ≤ 2*n := by
  induction n generalizing c with
  | zero => simp [limbsRun]
  | succ n ih =>
      rw [limbsRun_succ_trace]
      let r := limbRun H 8 c
      change (match r.2.1 with
        | none => r.1
        | some _ => r.1 ++ (limbsRun H n r.2.2).1).length ≤ 2 * (n + 1)
      have hr := limbRun_eight_bound H c
      change r.1.length ≤ 2 at hr
      cases h : r.2.1 with
      | none =>
          change r.1.length ≤ 2 * (n + 1)
          omega
      | some a =>
          have hn' : n ≤ 3 := by omega
          have ht := ih r.2.2 hn'
          change (r.1 ++ (limbsRun H n r.2.2).1).length ≤ 2 * (n + 1)
          simp only [List.length_append]
          omega

theorem limbsRun_four_initial_bound (H : Bytes → State) (c : Cursor)
    (h : c.index.val = 0) :
    (limbsRun H 4 c).1.length ≤ 6 := by
  rw [show 4 = 3 + 1 by omega, limbsRun_succ_trace]
  let r := limbRun H 8 c
  change (match r.2.1 with
    | none => r.1
    | some _ => r.1 ++ (limbsRun H 3 r.2.2).1).length ≤ 6
  have hr := limbRun_eight_initial_zero H c h
  change r.1.length = 0 at hr
  cases hresult : r.2.1 with
  | none =>
      change r.1.length ≤ 6
      omega
  | some a =>
      have ht := limbsRun_tail_bound H 3 r.2.2 (by omega)
      change (r.1 ++ (limbsRun H 3 r.2.2).1).length ≤ 6
      simp only [List.length_append]
      omega

theorem challengeRun_trace_bound (H : Bytes → State) (s : State) :
    (challengeRun H s).1.length ≤ 8 := by
  simp only [challengeRun]
  let p := step H s
  let tail := limbsRun H 4 ⟨p.2,p.1,0⟩
  have ht := limbsRun_four_initial_bound H ⟨p.2,p.1,0⟩ (by rfl)
  simp [p, tail, calls, List.length_append] at ht ⊢
  omega

theorem challengeProgram_within_tight (s : State) :
    Within 8 (challengeProgram s) := by
  intro H
  rw [challenge_exact]
  exact challengeRun_trace_bound H s

#print axioms limbRun_rollover_bound
#print axioms challengeRun_trace_bound
#print axioms challengeProgram_within_tight
end AspisV8R19.SamplerCursorTightBound
