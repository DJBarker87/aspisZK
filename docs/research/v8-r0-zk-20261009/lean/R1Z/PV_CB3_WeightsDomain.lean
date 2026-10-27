import Std
set_option autoImplicit false
namespace R1Z.PV_CB3_WeightsDomain

def digit (j d : Nat) : Nat := (j / 4^d) % 4

def row (j : Nat) : Nat :=
  digit j 0 * 64 + digit j 1 * 256 + digit j 2 * 16 + digit j 3 + digit j 4 * 4

theorem digit_bound (j d : Nat) : digit j d < 4 := Nat.mod_lt _ (by decide)

/-- Both S variants discard all bits above their five base-four digits. -/
theorem row_bound (j : Nat) : row j < 1024 := by
  have h0 := digit_bound j 0
  have h1 := digit_bound j 1
  have h2 := digit_bound j 2
  have h3 := digit_bound j 3
  have h4 := digit_bound j 4
  unfold row
  omega

def CanonicalIndex (kind j : Nat) : Prop := kind < 7 ∧ j < 1024

theorem tensor_index (kind : Nat) (hlo : 1 ≤ kind) (hhi : kind < 7) (h4 : kind ≠ 4) :
    (if kind < 4 then kind-1 else kind-2) < 5 := by
  split <;> omega

theorem extra_index (j : Nat) (h : j < 56) : j / 28 < 2 := by omega

theorem exponent_bound (j : Nat) : j % 28 < 28 := Nat.mod_lt _ (by decide)

theorem dense_index (kind b : Nat) (hk : 1 ≤ kind ∧ kind ≤ 3) (hb : b < 10) :
    kind-1 < 3 ∧ 9-b < 10 := by omega
#print axioms digit_bound
#print axioms row_bound
#print axioms tensor_index
#print axioms extra_index
#print axioms exponent_bound
#print axioms dense_index
end R1Z.PV_CB3_WeightsDomain
