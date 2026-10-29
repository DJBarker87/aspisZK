import R1Z.PV_RDB2D_SparseShape
namespace R1Z.PV_RDB2D_SparseAddress
set_option autoImplicit false

def row (pref trailing suffix : Nat) : Nat := pref*2^trailing+suffix

theorem bound (width trailing suffix pref : Nat) (split : width+trailing=10)
    (hs : suffix<2^trailing) (hp : pref<2^width) : row pref trailing suffix<1024 := by
  unfold row
  calc
    pref*2^trailing+suffix < (pref+1)*2^trailing := by
      rw [Nat.add_mul,Nat.one_mul];omega
    _ ≤ 2^width*2^trailing := Nat.mul_le_mul_right _ hp
    _ = 2^10 := by rw [←Nat.pow_add,split]
    _ = 1024 := rfl

theorem injective (trailing suffix a b : Nat) (hs : suffix<2^trailing)
    (h : row a trailing suffix=row b trailing suffix) : a=b := by
  unfold row at h
  have hp := Nat.two_pow_pos trailing
  have eq : a*2^trailing=b*2^trailing := by omega
  exact Nat.eq_of_mul_eq_mul_right hp eq

theorem ordered (trailing suffix a b : Nat) (h : a<b) :
    row a trailing suffix<row b trailing suffix := by
  unfold row
  exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos _)) _

theorem quotient (trailing suffix pref : Nat) (hs : suffix<2^trailing) :
    row pref trailing suffix/2^trailing=pref := by
  unfold row
  have hm : (pref*2^trailing+suffix)%2^trailing=suffix := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt hs]
  have hd := Nat.mod_add_div (pref*2^trailing+suffix) (2^trailing)
  rw [hm] at hd
  have eq : pref*2^trailing=2^trailing*((pref*2^trailing+suffix)/2^trailing) := by omega
  rw [Nat.mul_comm (2^trailing)] at eq
  exact (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos trailing) eq).symm


#print axioms bound
#print axioms injective
#print axioms ordered
#print axioms quotient
end R1Z.PV_RDB2D_SparseAddress
