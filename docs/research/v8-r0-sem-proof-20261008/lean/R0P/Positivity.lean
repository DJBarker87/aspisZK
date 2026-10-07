import R0P.Core

/-! # Part C, first target: integer positivity of the transfer outputs

Source facts used (pinned revision; each becomes a hypothesis to be
discharged by the G1/G4 row lemmas):

* value rows `r ∈ {1008, 1010, 1012}` (`add_value_lanes`, terminal 466–512):
  the 30 cells `A i r`, `A i (r+1)`, `A i (r xor 12)` for `i < 10` are Boolean
  and `A 10 r = rec r + 2^10·rec (r+1) + 2^20·rec (r xor 12)` with
  `rec q = Σ_{i<10} A i q · 2^i` (`reconstruct_10`, 168–173);
* conservation at row 1014 (513–518): `A 0 1014 = A 1 1014 + A 2 1014` and
  `A 0 1015 = A 1 1015`;
* copy links (`COPY_LINKS`, tags 1124073486–89, weight kind 0 = always on):
  `A 10 1008 = A 0 1014`, `A 10 1010 = A 1 1014`, `A 10 1012 = A 1 1015`,
  `A 2 1014 = A 0 1015`;
* slot 94 (`positive_transfer.rs::residual`): `A 1 1014 · A 1 1015 · A 3 1014 = 1`.

Conclusion: the input value equals recipient + change **as integers**, all
three are below 2^30, and recipient and change are at least 1.  Only
`CharP K (2^31 − 1)` is used, so it holds in QM31 without a typing premise. -/
set_option autoImplicit false
namespace R0P

open Finset

variable {K : Type} [Field K]

/-- `reconstruct_10` on a row: `Σ_{i<10} A i q · 2^i`. -/
def rec10 (f : Fin 10 → K) : K := ∑ i, f i * 2 ^ (i : Nat)

theorem bit_cases {b : K} (h : b * b = b) : b = 0 ∨ b = 1 := by
  have : b * (b - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

theorem rec10_nat (f : Fin 10 → K) (hb : ∀ i, f i * f i = f i) :
    ∃ n : Nat, n < 2 ^ 10 ∧ rec10 f = (n : K) := by
  classical
  let g : Fin 10 → Nat := fun i => if f i = 1 then 2 ^ (i : Nat) else 0
  refine ⟨∑ i, g i, ?_, ?_⟩
  · calc ∑ i, g i ≤ ∑ i : Fin 10, 2 ^ (i : Nat) := by
          apply Finset.sum_le_sum; intro i _; simp only [g]; split <;> simp
      _ < 2 ^ 10 := by simp [Fin.sum_univ_succ]
  · unfold rec10
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    simp only [g]
    rcases bit_cases (hb i) with h | h
    · have : f i ≠ 1 := by rw [h]; exact zero_ne_one
      rw [if_neg this, h]; simp
    · rw [if_pos h, h]; push_cast; ring

/-- A value row: three 10-bit blocks give a natural number below 2^30. -/
theorem value_nat (a b c : Fin 10 → K) (ha : ∀ i, a i * a i = a i) (hb : ∀ i, b i * b i = b i)
    (hc : ∀ i, c i * c i = c i) :
    ∃ n : Nat, n < 2 ^ 30 ∧ rec10 a + 2 ^ 10 * rec10 b + 2 ^ 20 * rec10 c = (n : K) := by
  obtain ⟨na, hna, ea⟩ := rec10_nat a ha
  obtain ⟨nb, hnb, eb⟩ := rec10_nat b hb
  obtain ⟨nc, hnc, ec⟩ := rec10_nat c hc
  refine ⟨na + 2 ^ 10 * nb + 2 ^ 20 * nc, by omega, ?_⟩
  rw [ea, eb, ec]; push_cast; ring

/-- The bits of value row `r` as three 10-bit blocks. -/
def blockAt (A : Trace K) (q : Fin 1024) : Fin 10 → K := fun i => A (Fin.castLE (by norm_num) i) q

/-- The value-row equations of `add_value_lanes` at row `r`. -/
def ValueRow (A : Trace K) (r : Fin 1024) : Prop :=
  (∀ i, blockAt A r i * blockAt A r i = blockAt A r i) ∧
  (∀ i, blockAt A (succRow r) i * blockAt A (succRow r) i = blockAt A (succRow r) i) ∧
  (∀ i, blockAt A (xor12Row r) i * blockAt A (xor12Row r) i = blockAt A (xor12Row r) i) ∧
  A 10 r = rec10 (blockAt A r) + 2 ^ 10 * rec10 (blockAt A (succRow r)) +
    2 ^ 20 * rec10 (blockAt A (xor12Row r))

theorem valueRow_nat (A : Trace K) (r : Fin 1024) (h : ValueRow A r) :
    ∃ n : Nat, n < 2 ^ 30 ∧ A 10 r = (n : K) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨n, hn, e⟩ := value_nat _ _ _ h1 h2 h3
  exact ⟨n, hn, h4.trans e⟩

/-- The positivity chain. -/
theorem positivity (P : Nat) [CharP K P] (hP : P = 2 ^ 31 - 1) (A : Trace K)
    (hv0 : ValueRow A 1008) (hv1 : ValueRow A 1010) (hv2 : ValueRow A 1012)
    (hcons0 : A 0 1014 = A 1 1014 + A 2 1014) (hcons1 : A 0 1015 = A 1 1015)
    (hc0 : A 10 1008 = A 0 1014) (hc1 : A 10 1010 = A 1 1014) (hc2 : A 10 1012 = A 1 1015)
    (hc3 : A 2 1014 = A 0 1015)
    (h94 : A 1 1014 * A 1 1015 * A 3 1014 = 1) :
    ∃ v0 v1 v2 : Nat, v0 < 2 ^ 30 ∧ v1 < 2 ^ 30 ∧ v2 < 2 ^ 30 ∧ 1 ≤ v1 ∧ 1 ≤ v2 ∧
      v0 = v1 + v2 ∧ A 0 1014 = (v0 : K) ∧ A 1 1014 = (v1 : K) ∧ A 1 1015 = (v2 : K) := by
  obtain ⟨v0, hv0lt, e0⟩ := valueRow_nat A 1008 hv0
  obtain ⟨v1, hv1lt, e1⟩ := valueRow_nat A 1010 hv1
  obtain ⟨v2, hv2lt, e2⟩ := valueRow_nat A 1012 hv2
  have a0 : A 0 1014 = (v0 : K) := hc0.symm.trans e0
  have a1 : A 1 1014 = (v1 : K) := hc1.symm.trans e1
  have a2 : A 1 1015 = (v2 : K) := hc2.symm.trans e2
  have hne1 : A 1 1014 ≠ 0 := fun h => by rw [h, zero_mul, zero_mul] at h94; exact zero_ne_one h94
  have hne2 : A 1 1015 ≠ 0 := fun h => by rw [h, mul_zero, zero_mul] at h94; exact zero_ne_one h94
  have p1 : 1 ≤ v1 := by
    rcases Nat.eq_zero_or_pos v1 with h | h
    · exact absurd (by rw [a1, h, Nat.cast_zero]) hne1
    · exact h
  have p2 : 1 ≤ v2 := by
    rcases Nat.eq_zero_or_pos v2 with h | h
    · exact absurd (by rw [a2, h, Nat.cast_zero]) hne2
    · exact h
  -- conservation as a field equation, then as integers
  have hfield : ((v0 : Nat) : K) = ((v1 + v2 : Nat) : K) := by
    push_cast
    rw [← a0, ← a1, ← a2, hcons0, hc3, hcons1]
  have hmod := (CharP.natCast_eq_natCast K P).mp hfield
  have hv : v0 = v1 + v2 := by
    subst hP
    exact Nat.ModEq.eq_of_lt_of_lt hmod (by omega) (by omega)
  exact ⟨v0, v1, v2, hv0lt, hv1lt, hv2lt, p1, p2, hv, a0, a1, a2⟩

#print axioms positivity
end R0P
