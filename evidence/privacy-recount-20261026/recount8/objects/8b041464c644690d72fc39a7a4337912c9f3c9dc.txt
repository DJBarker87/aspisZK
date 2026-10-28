import R1Z.QueryScanIndependentHistory

/-! Connect the independent-word event to the constructed parser's actual
first-stop failure. No scan recurrence or word universe is enumerated. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanFirstStopHistory
open R0Z.FsStatement R1Z.PhaseSamplerParserBin R1Z.PhaseQueryScanBin
  R1Z.QueryScanIndependentHistory AspisV8R19.Q22WordScan
attribute [local instance] Classical.propDecidable

theorem parsed_length (q : Fin 8 → OracleAnswer) (k : Fin 8) :
    (parsedWords q k).length = 8 * (k.val + 1) := by
  have hlen (bs : List OracleAnswer) : (bs.flatMap blockWords).length = 8 * bs.length := by
    induction bs with
    | nil => rfl
    | cons b bs ih => simp only [List.flatMap_cons, List.length_append, blockWords_length,
        ih, List.length_cons]; omega
  unfold parsedWords
  rw [hlen, List.length_take, List.length_ofFn, Nat.min_eq_left (by omega)]

theorem parsed_full_words64 (q : Fin 8 → OracleAnswer) :
    parsedWords q 7 = AspisR1.QueryScanModelFailure.words (words64 q) := by
  unfold parsedWords AspisR1.QueryScanModelFailure.words
  rw [show (7 : Fin 8).val + 1 = 8 from rfl,
    List.take_of_length_le (by rw [List.length_ofFn])]
  rw [List.ofFn_mul' (m := 8) (n := 8)]
  have he (bs : List OracleAnswer) : bs.flatMap blockWords = (bs.map blockWords).flatten := by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
        simp only [List.flatMap_cons, List.map_cons, List.flatten_cons]
        exact congrArg (fun t => blockWords b ++ t) ih
  rw [he, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext k
  change blockWords (q k) = List.ofFn (fun j : Fin 8 =>
    (words64 q ⟨8*k.val+j.val, by omega⟩).val)
  rw [block_le_words]
  apply congrArg List.ofFn
  funext j
  have hi : (⟨8*k.val+j.val, by omega⟩ : Fin 64) = finProdFinEquiv (k,j) := by
    apply Fin.ext
    change 8*k.val+j.val = j.val+8*k.val
    omega
  simp only [hi, words64, flatten, Equiv.coe_fn_mk, Equiv.symm_apply_apply]

/-- Read-count bound valid on stopped and non-stopped branches alike. -/
theorem scan_draws_le (s : ScanState) (xs : List ℕ) :
    (scan s xs).1.draws ≤ s.draws + xs.length := by
  induction xs generalizing s with
  | nil => simp only [scan, List.length_nil, Nat.add_zero, le_refl]
  | cons x xs ih =>
      by_cases hs : s.accepted.length = 22 ∨ s.draws = 64
      · simp only [scan, if_pos hs, List.length_cons]; omega
      · simp only [scan, if_neg hs, List.length_cons]
        have hh := ih ⟨keep s.accepted x, s.draws+1⟩
        dsimp only at hh
        omega

theorem selected_failure_at_last (q : Fin 8 → OracleAnswer) (count : ℕ)
    (hf : finish (scanned (stop done q) q).1 = .error count) : stop done q = 7 := by
  have hn : (scanned (stop done q) q).1.accepted.length ≠ 22 := by
    intro hh
    simp only [finish, hh, if_true] at hf
    cases hf
  have hm := (Finset.mem_filter.mp (stop_mem done q)).2
  rcases hm with hd | he
  · have heq : scanned (stop done q) (observed q (stop done q)) = scanned (stop done q) q := by
      unfold scanned
      rw [parsed_observed]
    change (scanned (stop done q) (observed q (stop done q))).2 = true at hd
    rw [heq] at hd
    have hst := AspisR1.QueryScanOrderedModel.scan_true_stopped
      AspisR1.QueryScanModelFailure.initial (parsedWords q (stop done q)) hd
    rcases hst with hlen | hdraw
    · exact False.elim (hn hlen)
    · change (scanned (stop done q) q).1.draws = 64 at hdraw
      have hh := scan_draws_le AspisR1.QueryScanModelFailure.initial (parsedWords q (stop done q))
      rw [parsed_length] at hh
      change (scanned (stop done q) q).1.draws ≤ 0 + 8 * ((stop done q).val+1) at hh
      have hk := (stop done q).isLt
      apply Fin.ext
      change (stop done q).val = 7
      omega
  · exact he

theorem selected_failure_implies_words_failure (q : Fin 8 → OracleAnswer) (count : ℕ)
    (hf : finish (scanned (stop done q) q).1 = .error count) :
    AspisR1.QueryScanModelFailure.fails (words64 q) := by
  rw [selected_failure_at_last q count hf] at hf
  unfold AspisR1.QueryScanModelFailure.fails
  rw [← parsed_full_words64]
  intro hlen
  simp only [scanned, finish, hlen, if_true] at hf
  cases hf

#print axioms parsed_length
#print axioms parsed_full_words64
#print axioms scan_draws_le
#print axioms selected_failure_at_last
#print axioms selected_failure_implies_words_failure
end R1Z.QueryScanFirstStopHistory
