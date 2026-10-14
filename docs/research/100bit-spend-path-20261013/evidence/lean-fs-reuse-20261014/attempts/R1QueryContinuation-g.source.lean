import R0C.V3.Q22Law

/-! Structural facts about the state selected by the bounded q22 scan.
These statements describe the returned state only; they make no claim about
independence or replacement by the final advance. -/

set_option autoImplicit false
namespace AspisR1.QueryContinuation

open R0C.V3 AspisV8R19.Q22WordScan AspisV8R19.Q22SamplerProgram

abbrev State := AspisV8R19.SourceDuplexStep.State
abbrev ScanState := AspisV8R19.Q22WordScan.ScanState

theorem scanOut_state_mem : ∀ (n : Nat) (q : ScanState)
    (bs xs : List State) (s : State),
    (Q22.scanOut n q bs xs s).2 ∈ s :: xs := by
  intro n
  induction n with
  | zero =>
      intro q bs xs s
      simp [Q22.scanOut]
  | succ n ih =>
      intro q bs xs s
      cases bs with
      | nil =>
          simp [Q22.scanOut]
      | cons b bs =>
          cases xs with
          | nil =>
              simp [Q22.scanOut]
          | cons x xs =>
              by_cases hdraw : q.draws < 64
              · simp only [Q22.scanOut, if_pos hdraw]
                by_cases hstop : (AspisV8R19.Q22WordScan.scan q
                    (AspisV8R19.SamplerWords.words 18 b)).2 = true
                · simp [hstop]
                · simp only [hstop]
                  exact List.mem_cons_of_mem s (ih (AspisV8R19.Q22WordScan.scan q
                    (AspisV8R19.SamplerWords.words 18 b)).1 bs xs x)
              · simp [Q22.scanOut, hdraw]

theorem scanOut_succ_cons_state_mem
    (n : Nat) (q : ScanState) (b : State) (bs : List State)
    (x : State) (xs : List State) (s : State)
    (hdraw : q.draws < 64) :
    (Q22.scanOut (n + 1) q (b :: bs) (x :: xs) s).2 ∈ x :: xs := by
  simp only [Q22.scanOut, if_pos hdraw]
  by_cases hstop : (AspisV8R19.Q22WordScan.scan q
      (AspisV8R19.SamplerWords.words 18 b)).2 = true
  · simp [hstop]
  · simp only [hstop]
    simpa [hstop] using scanOut_state_mem n (AspisV8R19.Q22WordScan.scan q
      (AspisV8R19.SamplerWords.words 18 b)).1 bs xs x

theorem eight_pair_continuation
    (bs xs : List State) (s : State)
    (hbs : bs.length = 8) (hxs : xs.length = 8) :
    (Q22.scanOut 8 Q22.q0 bs xs s).2 ∈ xs := by
  cases bs with
  | nil => simp at hbs
  | cons b bs =>
      cases xs with
      | nil => simp at hxs
      | cons x xs =>
          have hdraw : Q22.q0.draws < 64 := by decide
          have hmem := scanOut_succ_cons_state_mem 7 Q22.q0 b bs x xs s hdraw
          have hlen : (x :: xs).length = 8 := hxs
          simpa using hmem

#print axioms scanOut_state_mem
#print axioms scanOut_succ_cons_state_mem
#print axioms eight_pair_continuation

end AspisR1.QueryContinuation
