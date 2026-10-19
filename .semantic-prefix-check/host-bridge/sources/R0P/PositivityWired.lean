import R0P.Positivity
import R0P.Value
import R0P.Positive

/-! # Positivity from the literal G1 ports

`positivity_of_families`: if the literal Value and Positive families hold
(G1's `value_holds_iff`, `positive_holds_iff`) and the four always-enabled
copy links into rows 1014/1015 hold, the transfer's input equals recipient +
change as integers, all below 2^30, recipient and change at least 1.  The only
remaining hypotheses are the four copy equalities, which the copy relation
(G4 + LogUp) must deliver. -/
set_option autoImplicit false
namespace R0P

variable {K : Type} [Field K]

theorem rec10_explicit (f : Fin 10 → K) :
    rec10 f = f 0 + 2 * f 1 + 4 * f 2 + 8 * f 3 + 16 * f 4 + 32 * f 5 +
      64 * f 6 + 128 * f 7 + 256 * f 8 + 512 * f 9 := by
  simp only [rec10, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  ring

theorem rec10_blockAt (A : Trace K) (q : Fin 1024) :
    rec10 (blockAt A q) = A 0 q + 2 * A 1 q + 4 * A 2 q + 8 * A 3 q + 16 * A 4 q + 32 * A 5 q +
      64 * A 6 q + 128 * A 7 q + 256 * A 8 q + 512 * A 9 q := by
  rw [rec10_explicit]
  rfl

theorem blockAt_bool (A : Trace K) (q : Fin 1024)
    (h : ∀ i : Fin 10, A (i.castAdd 19) q = 0 ∨ A (i.castAdd 19) q = 1) :
    ∀ i, blockAt A q i * blockAt A q i = blockAt A q i := by
  intro i
  have e : (Fin.castLE (by norm_num) i : Fin 29) = i.castAdd 19 := Fin.ext rfl
  simp only [blockAt, e]
  rcases h i with h0 | h1
  · rw [h0, mul_zero]
  · rw [h1, mul_one]

theorem valueRow_of_holds (pub : Public K) (A : Trace K) (h : Holds valueFamily pub A)
    (r : Fin 1024) (hr : r = 1008 ∨ r = 1010 ∨ r = 1012) : ValueRow A r := by
  obtain ⟨hrows, _, _⟩ := (value_holds_iff pub A).mp h
  obtain ⟨hb0, hb1, hb2, hrec, _, _⟩ := hrows r hr
  refine ⟨blockAt_bool A r hb0, blockAt_bool A _ hb1, blockAt_bool A _ hb2, ?_⟩
  rw [hrec, rec10_blockAt, rec10_blockAt, rec10_blockAt]
  ring

theorem positivity_of_families (P : Nat) [CharP K P] (hP : P = 2 ^ 31 - 1) (pub : Public K)
    (A : Trace K) (hv : Holds valueFamily pub A) (hpos : Holds positiveFamily pub A)
    (hc0 : A 10 1008 = A 0 1014) (hc1 : A 10 1010 = A 1 1014) (hc2 : A 10 1012 = A 1 1015)
    (hc3 : A 2 1014 = A 0 1015) :
    ∃ v0 v1 v2 : Nat, v0 < 2 ^ 30 ∧ v1 < 2 ^ 30 ∧ v2 < 2 ^ 30 ∧ 1 ≤ v1 ∧ 1 ≤ v2 ∧
      v0 = v1 + v2 ∧ A 0 1014 = (v0 : K) ∧ A 1 1014 = (v1 : K) ∧ A 1 1015 = (v2 : K) := by
  obtain ⟨_, hcons0, hcons1⟩ := (value_holds_iff pub A).mp hv
  exact positivity P hP A (valueRow_of_holds pub A hv 1008 (Or.inl rfl))
    (valueRow_of_holds pub A hv 1010 (Or.inr (Or.inl rfl)))
    (valueRow_of_holds pub A hv 1012 (Or.inr (Or.inr rfl)))
    hcons0 hcons1 hc0 hc1 hc2 hc3 ((positive_holds_iff pub A).mp hpos)

#print axioms positivity_of_families
end R0P
