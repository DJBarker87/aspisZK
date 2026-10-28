import R1Z.ProverRwQueryContains

/-! Exact prefix membership for the emitted duplicate test, including totality. -/
set_option autoImplicit false
namespace R1Z.ProverRwQueryMembership
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryContains

theorem search_success_iff (accepted : Queries) (candidate : U32)
    (fuel : Nat) (index : Usize) (size : index.val+fuel ≤ 22) :
    search accepted candidate fuel index = some true ↔
      ∃ j, index.val ≤ j ∧ j < index.val+fuel ∧ accepted.val[j]? = some candidate := by
  induction fuel generalizing index with
  | zero => simp only [search,reduceCtorEq]; constructor <;> intro h
            · contradiction
            · obtain ⟨j,lo,hi,_⟩ := h; omega
  | succ fuel ih =>
    have add : (Usize.wrapping_add index 1#usize).val = index.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      have one : (1#usize).val = 1 := rfl
      rw [one,Nat.mod_eq_of_lt]
      have big := (22#usize).hSize
      change 22 < UScalar.size .Usize at big
      omega
    by_cases hit : accepted.val[index.val]? = some candidate
    · simp only [search,hit,if_true,true_iff]
      exact ⟨index.val,by omega,by omega,hit⟩
    · simp only [search,hit,if_false]
      rw [ih _ (by omega)]
      constructor
      · rintro ⟨j,lo,hi,hj⟩
        exact ⟨j,by omega,by omega,hj⟩
      · rintro ⟨j,lo,hi,hj⟩
        have ne : j ≠ index.val := by intro eq; subst j; exact hit hj
        exact ⟨j,by omega,by omega,hj⟩

theorem search_ne_false (accepted : Queries) (candidate : U32)
    (fuel : Nat) (index : Usize) :
    search accepted candidate fuel index ≠ some false := by
  induction fuel generalizing index with
  | zero => simp only [search,ne_eq,reduceCtorEq,not_false_eq_true]
  | succ fuel ih =>
    unfold search
    split
    · decide
    · exact ih _

theorem contains_prefix_iff (accepted : Queries) (n : Usize) (candidate : U32)
    (size : n.val ≤ 22) :
    host_transcript.query_contains accepted n candidate = ok true ↔
      ∃ j, j < n.val ∧ accepted.val[j]? = some candidate := by
  rw [contains_exact accepted n candidate size]
  have hs := search_success_iff accepted candidate n.val 0#usize (by simpa using size)
  have hn := search_ne_false accepted candidate n.val 0#usize
  have hz : (0#usize).val = 0 := rfl
  simp only [hz,Nat.zero_add,Nat.zero_le,true_and] at hs
  unfold contains
  cases h : search accepted candidate n.val 0#usize with
  | none => simp only [h,reduceCtorEq,false_iff] at hs; simpa only [h,Option.getD_none,Result.ok.injEq,Bool.false_eq_true,false_iff] using hs
  | some b =>
    cases b with
    | false => exact False.elim (hn h)
    | true => simpa only [h,Option.getD_some,Result.ok.injEq,true_iff] using hs

#print axioms search_success_iff
#print axioms search_ne_false
#print axioms contains_prefix_iff
end R1Z.ProverRwQueryMembership
