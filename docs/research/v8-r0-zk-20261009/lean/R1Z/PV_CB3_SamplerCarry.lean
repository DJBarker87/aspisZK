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

#print axioms length_preserved
#print axioms value_conserved
#print axioms digits_canonical
end R1Z.PV_CB3_SamplerCarry
