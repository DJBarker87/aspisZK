import R1QueryContinuation

/-! Prefix truncation for the q22 scan, under the exact premise that its
selected continuation state is absent from the omitted advance suffix. -/

set_option autoImplicit false
namespace AspisR1.QueryTruncation

open R0C.V3 AspisV8R19.Q22WordScan AspisV8R19.Q22SamplerProgram

abbrev State := AspisV8R19.SourceDuplexStep.State
abbrev ScanState := AspisV8R19.Q22WordScan.ScanState

theorem scanOut_truncate (n k : Nat) (q : ScanState)
    (bs xs : List State) (s : State) (hk : k ≤ n)
    (htail : (Q22.scanOut n q bs xs s).2 ∉ xs.drop k) :
    Q22.scanOut k q (bs.take k) (xs.take k) s =
      Q22.scanOut n q bs xs s := by
  induction n generalizing k q bs xs s with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp [Q22.scanOut]
  | succ n ih =>
      cases k with
      | zero =>
          cases bs with
          | nil => simp [Q22.scanOut]
          | cons b bs =>
              cases xs with
              | nil => simp [Q22.scanOut]
              | cons x xs =>
                  by_cases hdraw : q.draws < 64
                  · have hmem := AspisR1.QueryContinuation.scanOut_succ_cons_state_mem
                      n q b bs x xs s hdraw
                    have hnot : (Q22.scanOut (n + 1) q (b :: bs) (x :: xs) s).2 ∉ x :: xs := by
                      simpa using htail
                    exact False.elim (hnot hmem)
                  · simp [Q22.scanOut, hdraw]
      | succ k =>
          have hk' : k ≤ n := by omega
          cases bs with
          | nil => simp [Q22.scanOut]
          | cons b bs =>
              cases xs with
              | nil => simp [Q22.scanOut]
              | cons x xs =>
                  by_cases hdraw : q.draws < 64
                  · simp only [Q22.scanOut, if_pos hdraw]
                    by_cases hstop : (AspisV8R19.Q22WordScan.scan q
                        (AspisV8R19.SamplerWords.words 18 b)).2 = true
                    · simp [Q22.scanOut, hdraw, hstop, List.take_succ_cons]
                    · have htail' :
                          (Q22.scanOut n
                            (AspisV8R19.Q22WordScan.scan q
                              (AspisV8R19.SamplerWords.words 18 b)).1
                            bs xs x).2 ∉ xs.drop k := by
                        simpa [Q22.scanOut, hdraw, hstop,
                          List.drop_succ_cons] using htail
                      have hrec := ih k
                        (AspisV8R19.Q22WordScan.scan q
                          (AspisV8R19.SamplerWords.words 18 b)).1
                        bs xs x hk' htail'
                      simpa [Q22.scanOut, hdraw, hstop,
                        List.take_succ_cons] using hrec
                  · simp [Q22.scanOut, hdraw, List.take_succ_cons]

#print axioms scanOut_truncate

end AspisR1.QueryTruncation
