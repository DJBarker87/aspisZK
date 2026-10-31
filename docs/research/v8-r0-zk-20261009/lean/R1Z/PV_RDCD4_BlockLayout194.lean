import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RDCD4_BlockLayout194
/-- Source repr(C) byte storage: one u8 leaf; even nodes concatenate two
parents and a zero-sized PhantomData marker. Concrete ABI preservation is V370. -/
def byteSize : Nat → Nat
  | 0 => 1
  | k+1 => 2*byteSize k

theorem size_power (k : Nat) : byteSize k=2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [byteSize,ih,Nat.pow_succ,Nat.mul_comm]

theorem size64 : byteSize 6=64 := by rw [size_power];rfl

def consumed (n : Nat) : Nat := (n/64)*64

theorem bounded (n : Nat) : consumed n ≤ n := Nat.div_mul_le_self n 64

theorem remainder (n : Nat) : n-consumed n=n%64 := by
  have h := Nat.mod_add_div n 64
  have comm : 64*(n/64)=(n/64)*64 := Nat.mul_comm _ _
  unfold consumed
  omega

theorem tail_bound (n : Nat) : n-consumed n < 64 := by
  rw [remainder]
  exact Nat.mod_lt n (by omega)

theorem word_bounds (n : Nat) (h : n < 2^64) :
    consumed n < 2^64 ∧ n/64 < 2^64 ∧ n-consumed n < 2^64 := by
  have hb := bounded n
  have hq := Nat.div_le_self n 64
  omega
#print axioms size_power
#print axioms size64
#print axioms bounded
#print axioms remainder
#print axioms tail_bound
#print axioms word_bounds
end R1Z.PV_RDCD4_BlockLayout194
