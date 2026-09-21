import Mathlib.Data.Nat.Bitwise

/-! Index-only source schedule: weights are represented by their exponent
of one half. Ten fuel units suffice for the two concrete input lengths.
No field arithmetic, challenge, witness or recurrence normalization. -/
set_option autoImplicit false
namespace AspisV8R17

def indexLoop : ℕ → ℕ → ℕ → Option (List (ℕ × ℕ))
  | 0, _, _ => none
  | fuel+1, row, bit =>
      if row &&& (2^bit) != 0 then
        let next := row ^^^ (2^bit)
        (indexLoop fuel next (bit+1)).map (fun rest => (next,bit+1)::rest)
      else some [(row ||| (2^bit),bit)]

def scheduleBounded (n : ℕ) : Bool :=
  (List.range ((n+15)/16)).all fun block =>
    (List.range 16).all fun offset =>
      let j := block*16+offset
      if j<n then
        match indexLoop 10 j 0 with
        | none => false
        | some edges => edges.all fun e => e.1 ≤ n && e.2 ≤ 9
      else true

theorem schedule512_bounded : scheduleBounded 512 = true := by decide
theorem schedule513_bounded : scheduleBounded 513 = true := by decide

theorem scheduleBounded_sound (n j : ℕ) (h : scheduleBounded n = true) (hj : j<n) :
    ∃ edges, indexLoop 10 j 0 = some edges ∧ ∀ e ∈ edges, e.1≤n ∧ e.2≤9 := by
  simp only [scheduleBounded, List.all_eq_true, List.mem_range] at h
  have hb : j/16 < (n+15)/16 := by omega
  have ho : j%16 < 16 := Nat.mod_lt _ (by decide)
  have hs := h (j/16) hb (j%16) ho
  have he : j/16*16+j%16=j := by omega
  simp only [he, if_pos hj] at hs
  cases hl : indexLoop 10 j 0 with
  | none => simp [hl] at hs
  | some edges =>
      refine ⟨edges,rfl,?_⟩
      simpa only [hl, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] using hs

theorem source512_index_bounds (j : ℕ) (hj : j<512) :
    ∃ edges, indexLoop 10 j 0 = some edges ∧ ∀ e ∈ edges, e.1<513 ∧ e.2≤9 := by
  obtain ⟨edges,he,hb⟩ := scheduleBounded_sound 512 j schedule512_bounded hj
  exact ⟨edges,he,fun e hm => ⟨Nat.lt_succ_of_le (hb e hm).1,(hb e hm).2⟩⟩

theorem source513_index_bounds (j : ℕ) (hj : j<513) :
    ∃ edges, indexLoop 10 j 0 = some edges ∧ ∀ e ∈ edges, e.1<514 ∧ e.2≤9 := by
  obtain ⟨edges,he,hb⟩ := scheduleBounded_sound 513 j schedule513_bounded hj
  exact ⟨edges,he,fun e hm => ⟨Nat.lt_succ_of_le (hb e hm).1,(hb e hm).2⟩⟩

#print axioms scheduleBounded_sound
#print axioms source512_index_bounds
#print axioms source513_index_bounds
#print axioms schedule512_bounded
#print axioms schedule513_bounded
end AspisV8R17
