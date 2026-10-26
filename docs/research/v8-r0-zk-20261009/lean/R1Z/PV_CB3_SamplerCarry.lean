import Std
namespace R1Z.PV_CB3_SamplerCarry
set_option autoImplicit false

/-- Little-endian digit value; symbolic in the base and length. -/
def value (base : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + base * value base ds

/-- Owned mathematical carry recurrence, with the final carry retained. -/
def addCarry (base : Nat) : List Nat → Nat → List Nat × Nat
  | [], carry => ([], carry)
  | d :: ds, carry =>
    let next := addCarry base ds ((d + carry) / base)
    ((d + carry) % base :: next.1, next.2)

theorem length_preserved (base : Nat) (digits : List Nat) (carry : Nat) :
    (addCarry base digits carry).1.length = digits.length := by
  induction digits generalizing carry with
  | nil => rfl
  | cons d ds ih => simp only [addCarry, List.length_cons, ih]

/-- Exact value conservation, including overflow beyond the final digit. -/
theorem value_conserved (base : Nat) (digits : List Nat) (carry : Nat) :
    value base (addCarry base digits carry).1 +
      base ^ digits.length * (addCarry base digits carry).2 =
      value base digits + carry := by
  induction digits generalizing carry with
  | nil => simp only [addCarry, value, List.length_nil, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | cons d ds ih =>
    simp only [addCarry, value, List.length_cons]
    calc
      _ = (d + carry) % base + base *
          (value base (addCarry base ds ((d + carry) / base)).1 +
            base ^ ds.length * (addCarry base ds ((d + carry) / base)).2) := by
        simp only [Nat.pow_succ, Nat.mul_add]
        ac_rfl
      _ = (d + carry) % base + base * (value base ds + (d + carry) / base) := by
        rw [ih]
      _ = ((d + carry) % base + base * ((d + carry) / base)) + base * value base ds := by
        simp only [Nat.mul_add]
        ac_rfl
      _ = (d + carry) + base * value base ds := by rw [Nat.mod_add_div]
      _ = d + base * value base ds + carry := by omega

theorem digits_canonical (base : Nat) (positive : 0 < base)
    (digits : List Nat) (carry : Nat) :
    ∀ d, d ∈ (addCarry base digits carry).1 → d < base := by
  induction digits generalizing carry with
  | nil => intro d h; simp only [addCarry, List.not_mem_nil] at h
  | cons x xs ih =>
    intro d h
    simp only [addCarry, List.mem_cons] at h
    rcases h with h | h
    · subst d
      exact Nat.mod_lt _ positive
    · exact ih _ d h

/-- Canonical digits have the expected radix bound for every length. -/
theorem value_lt_pow (base : Nat) (positive : 0 < base) (digits : List Nat)
    (canonical : ∀ d, d ∈ digits → d < base) :
    value base digits < base ^ digits.length := by
  revert canonical
  induction digits with
  | nil => intro _; simp only [value, List.length_nil, Nat.pow_zero]; omega
  | cons d ds ih =>
    intro canonical
    have hd := canonical d (List.mem_cons_self ..)
    have ht := ih (fun x hx => canonical x (List.mem_cons_of_mem d hx))
    have hm := Nat.mul_le_mul_left base (Nat.succ_le_of_lt ht)
    simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hm
    simp only [value, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_comm (base ^ ds.length) base]
    omega

/-- The retained overflow is exactly the quotient, not a guessed Boolean. -/
theorem carry_quotient (base : Nat) (positive : 0 < base)
    (digits : List Nat) (carry : Nat) :
    (value base digits + carry) / base ^ digits.length =
      (addCarry base digits carry).2 := by
  have bound := value_lt_pow base positive (addCarry base digits carry).1
    (digits_canonical base positive digits carry)
  rw [length_preserved] at bound
  rw [← value_conserved base digits carry]
  rw [Nat.add_mul_div_left _ _ (Nat.pow_pos positive), Nat.div_eq_of_lt bound]
  rfl

/-- The stored digits are exactly the low part modulo the full radix power. -/
theorem digits_remainder (base : Nat) (positive : 0 < base)
    (digits : List Nat) (carry : Nat) :
    (value base digits + carry) % base ^ digits.length =
      value base (addCarry base digits carry).1 := by
  have bound := value_lt_pow base positive (addCarry base digits carry).1
    (digits_canonical base positive digits carry)
  rw [length_preserved] at bound
  rw [← value_conserved base digits carry, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt bound]

#print axioms length_preserved
#print axioms value_conserved
#print axioms digits_canonical
#print axioms value_lt_pow
#print axioms carry_quotient
#print axioms digits_remainder
end R1Z.PV_CB3_SamplerCarry
