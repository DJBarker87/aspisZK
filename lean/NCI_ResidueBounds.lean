import Init
set_option autoImplicit false
namespace AspisR1.NCI_ResidueBounds

def P : Nat := 2147483647
def Boundary : Nat := 17179869184
def MaxProduct : Nat := 4611686009837453316

theorem product_bound (a b : Nat) (ha : a < P) (hb : b < P) :
    a*b ≤ MaxProduct := by
  have h := Nat.mul_le_mul (show a ≤ 2147483646 by simp [P] at ha; omega)
    (show b ≤ 2147483646 by simp [P] at hb; omega)
  exact h

theorem group_nowrap (raw product terms : Nat)
    (ht : terms < 4) (hr : raw < Boundary + terms*MaxProduct)
    (hp : product ≤ MaxProduct) : raw+product < 18446744073709551616 := by
  have hm : terms*MaxProduct ≤ 3*MaxProduct := Nat.mul_le_mul_right _ (by omega)
  simp only [Boundary,MaxProduct] at *
  omega

theorem next_partial (raw product terms : Nat)
    (hr : raw < Boundary + terms*MaxProduct) (hp : product ≤ MaxProduct) :
    raw+product < Boundary + (terms+1)*MaxProduct := by
  rw [Nat.add_mul]
  omega

theorem fold_boundary (raw : Nat) (h : raw < 18446744073709551616) :
    raw % 2147483648 + raw / 2147483648 < Boundary := by
  have hm := Nat.mod_lt raw (show 0 < 2147483648 by decide)
  have hd : raw / 2147483648 < 8589934592 :=
    (Nat.div_lt_iff_lt_mul (by decide)).mpr h
  simp only [Boundary]
  omega

theorem flush_schedule (terms : Nat) : terms % 4 = 3 → (terms+1)%4 = 0 := by omega

theorem twelve_queries (next : Nat) (h : 10 ≤ next ∧ next < 22) : next+1 ≤ 22 := by omega
#print axioms product_bound
#print axioms group_nowrap
#print axioms next_partial
#print axioms fold_boundary
#print axioms flush_schedule
#print axioms twelve_queries
end AspisR1.NCI_ResidueBounds
