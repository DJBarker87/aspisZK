import R1Z.PV_CB3_SamplerCarry
namespace R1Z.PV_CB3_SamplerDivision
open PV_CB3_SamplerCarry (value)
set_option autoImplicit false

/-- Little-endian long division: visit the high tail first, retaining the full
quotient vector and the final remainder. No numeral or recurrence is evaluated. -/
def divideLE (base radix : Nat) : List Nat → List Nat × Nat
  | [] => ([], 0)
  | word :: words =>
    let high := divideLE base radix words
    let n := high.2 * radix + word
    (n / base :: high.1, n % base)

theorem length_preserved (base radix : Nat) (words : List Nat) :
    (divideLE base radix words).1.length = words.length := by
  induction words with
  | nil => rfl
  | cons w ws ih => simp only [divideLE, List.length_cons, ih]

theorem remainder_lt (base radix : Nat) (positive : 0 < base) (words : List Nat) :
    (divideLE base radix words).2 < base := by
  cases words with
  | nil => exact positive
  | cons w ws => exact Nat.mod_lt _ positive

/-- Exact conservation of every quotient word, for arbitrary vector lengths. -/
theorem value_conserved (base radix : Nat) (words : List Nat) :
    base * value radix (divideLE base radix words).1 + (divideLE base radix words).2 =
      value radix words := by
  induction words with
  | nil => simp only [divideLE, value, Nat.mul_zero, Nat.add_zero]
  | cons w ws ih =>
    cases h : divideLE base radix ws with
    | mk q r =>
      rw [h] at ih
      simp only [divideLE, h, value]
      calc
        _ = ((r * radix + w) % base + base * ((r * radix + w) / base)) +
            radix * (base * value radix q) := by
          simp only [Nat.mul_add]
          ac_rfl
        _ = r * radix + w + radix * (base * value radix q) := by rw [Nat.mod_add_div]
        _ = w + radix * (base * value radix q + r) := by
          simp only [Nat.mul_add]
          ac_rfl
        _ = w + radix * value radix ws := by rw [ih]

theorem word_quotient_bound (base radix remainder word : Nat)
    (positive : 0 < base) (hr : remainder < base) (hw : word < radix) :
    (remainder * radix + word) / base < radix := by
  apply (Nat.div_lt_iff_lt_mul positive).2
  have hm := Nat.mul_le_mul_right radix (Nat.succ_le_of_lt hr)
  simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at hm
  calc
    remainder * radix + word < base * radix := by omega
    _ = radix * base := Nat.mul_comm _ _

theorem quotient_canonical (base radix : Nat) (positive : 0 < base) (words : List Nat)
    (canonical : ∀ w, w ∈ words → w < radix) :
    ∀ q, q ∈ (divideLE base radix words).1 → q < radix := by
  revert canonical
  induction words with
  | nil => intro _ q h; simp only [divideLE, List.not_mem_nil] at h
  | cons w ws ih =>
    intro canonical q h
    simp only [divideLE, List.mem_cons] at h
    rcases h with h | h
    · subst q
      exact word_quotient_bound base radix _ w positive
        (remainder_lt base radix positive ws) (canonical w (List.mem_cons_self ..))
    · exact ih (fun x hx => canonical x (List.mem_cons_of_mem w hx)) q h

/-- Complete scalar quotient and remainder, not just a conservation residual. -/
theorem quotient_value (base radix : Nat) (positive : 0 < base) (words : List Nat) :
    value radix words / base = value radix (divideLE base radix words).1 := by
  rw [← value_conserved base radix words]
  rw [Nat.add_comm (base * value radix (divideLE base radix words).1),
    Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt (remainder_lt base radix positive words)]
  exact Nat.zero_add _

theorem remainder_value (base radix : Nat) (positive : 0 < base) (words : List Nat) :
    value radix words % base = (divideLE base radix words).2 := by
  rw [← value_conserved base radix words]
  rw [Nat.add_comm (base * value radix (divideLE base radix words).1),
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (remainder_lt base radix positive words)]

#print axioms length_preserved
#print axioms remainder_lt
#print axioms value_conserved
#print axioms word_quotient_bound
#print axioms quotient_canonical
#print axioms quotient_value
#print axioms remainder_value
end R1Z.PV_CB3_SamplerDivision
