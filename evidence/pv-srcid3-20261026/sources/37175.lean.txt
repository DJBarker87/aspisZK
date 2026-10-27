import R1Z.PV_Src_LowBits

/-! Symbolic little-endian path-index packing; no concrete index recurrence
is kernel-normalized. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PathPacking

def pack : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat + 2*pack bs

theorem bound (bs : List Bool) : pack bs < 2^bs.length := by
  induction bs with
  | nil => simp [pack]
  | cons b bs ih =>
    cases b <;> simp only [pack,List.length_cons,Bool.toNat_false,Bool.toNat_true,pow_succ] <;> omega

theorem half (b : Bool) (bs : List Bool) : pack (b::bs) / 2 = pack bs := by
  cases b <;> simp only [pack,Bool.toNat_false,Bool.toNat_true] <;> omega

theorem bit (bs : List Bool) (k : Nat) (hk : k < bs.length) :
    pack bs / 2^k % 2 = (bs[k]!).toNat := by
  induction bs generalizing k with
  | nil => simp at hk
  | cons b bs ih =>
    cases k with
    | zero => cases b <;> simp only [pack,pow_zero,Nat.div_one,List.getElem!_cons_zero,
        Bool.toNat_false,Bool.toNat_true] <;> omega
    | succ k =>
      have hd : pack (b::bs) / 2^(k+1) = (pack (b::bs) / 2) / 2^k := by
        rw [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm (2^k) 2]
      rw [hd,half]
      simpa only [List.getElem!_cons_succ] using ih k (by simpa using hk)

#print axioms bound
#print axioms half
#print axioms bit
end R1Z.PV_Src_PathPacking
