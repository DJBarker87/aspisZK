import R1Z.PV_RDB2C_R1SamplerMachineBounds
import Mathlib.Data.Nat.Bitwise

set_option autoImplicit false

namespace AspisR1.SamplerWord

open AspisR1.SamplerMachineBounds

theorem packNat_of_lt (r d n : Nat) (hd : d < 2 ^ n) :
    Nat.shiftLeft r n ||| d = r * 2 ^ n + d := by
  calc
    Nat.shiftLeft r n ||| d = Nat.shiftLeft r n + d :=
      (Nat.shiftLeft_add_eq_or_of_lt hd r).symm
    _ = r * 2 ^ n + d := by
      change (r <<< n) + d = r * 2 ^ n + d
      rw [Nat.shiftLeft_eq]

theorem packNat (r d : Nat) (hd : d < 2 ^ 32) :
    Nat.shiftLeft r 32 ||| d = r * 2 ^ 32 + d :=
  packNat_of_lt r d 32 hd

theorem packNat_lt_two63 {r d : Nat} (hr : r < P) (hd : d < 2 ^ 32) :
    Nat.shiftLeft r 32 ||| d < 2 ^ 63 := by
  rw [packNat r d hd]
  exact dividend_lt_two63 hr (by simpa [B] using hd)

theorem modelExpr_lt_two63 {r d : Nat} (hr : r < P) (hd : d < 2 ^ 32) :
    r * 2 ^ 32 + d < 2 ^ 63 := by
  simpa [B] using dividend_lt_two63 hr (by simpa [B] using hd)

theorem modelExpr_UInt64_roundtrip {r d : Nat}
    (hr : r < P) (hd : d < 2 ^ 32) :
    (UInt64.ofNat (r * 2 ^ 32 + d)).toNat = r * 2 ^ 32 + d := by
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  exact lt_trans (modelExpr_lt_two63 hr hd) (by norm_num)

def machineWord (r : UInt64) (d : UInt32) : UInt64 :=
  (r <<< UInt64.ofNat 32) ||| UInt64.ofNat d.toNat

theorem machineWord_toNat {r : UInt64} (d : UInt32) (hr : r.toNat < P) :
    (machineWord r d).toNat = r.toNat * 2 ^ 32 + d.toNat := by
  have hd : d.toNat < 2 ^ 32 := UInt32.toNat_lt d
  have hmul : r.toNat * 2 ^ 32 < 2 ^ 63 := by
    calc
      r.toNat * 2 ^ 32 < P * B := by
        exact (Nat.mul_lt_mul_of_pos_right hr (by norm_num : 0 < 2 ^ 32)).trans_eq
          (by rfl)
      _ < 2 ^ 63 := P_times_B_lt_two63
  have hshift : Nat.shiftLeft r.toNat 32 < 2 ^ 64 := by
    change (r.toNat <<< 32) < 2 ^ 64
    rw [Nat.shiftLeft_eq]
    exact lt_trans hmul (by norm_num)
  have hshift' : r.toNat <<< 32 < 2 ^ 64 := by
    change Nat.shiftLeft r.toNat 32 < 2 ^ 64
    exact hshift
  have hpow64 : 2 ^ 64 = 18446744073709551616 := by norm_num
  rw [hpow64] at hshift'
  unfold machineWord
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft]
  simp only [UInt64.toNat_ofNat']
  norm_num
  rw [Nat.mod_eq_of_lt hshift']
  exact packNat r.toNat d.toNat hd

theorem machineWord_lt_two63 {r : UInt64} (d : UInt32) (hr : r.toNat < P) :
    (machineWord r d).toNat < 2 ^ 63 := by
  rw [machineWord_toNat d hr]
  exact modelExpr_lt_two63 hr (UInt32.toNat_lt d)

def machineStep (r : UInt64) (d : UInt32) : UInt32 × UInt32 :=
  let word := machineWord r d
  (UInt32.ofNat (word / UInt64.ofNat P).toNat,
   UInt32.ofNat (word % UInt64.ofNat P).toNat)

theorem machineStep_quotient_toNat {r : UInt64} (d : UInt32) (hr : r.toNat < P) :
    (machineStep r d).1.toNat = (r.toNat * 2 ^ 32 + d.toNat) / P := by
  have hd : d.toNat < 2 ^ 32 := UInt32.toNat_lt d
  have hq : (r.toNat * B + d.toNat) / P < B := dividend_quotient_lt_B hr hd
  have hq32 : (r.toNat * B + d.toNat) / P < 2 ^ 32 := by simpa [B] using hq
  have hP64 : P < 2 ^ 64 := by norm_num [P]
  simp only [machineStep, UInt32.toNat_ofNat', UInt64.toNat_div, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt hP64, machineWord_toNat d hr]
  have hq32' : (r.toNat * 2 ^ 32 + d.toNat) / P < 2 ^ 32 := by
    simpa [B] using hq32
  rw [Nat.mod_eq_of_lt hq32']

theorem machineStep_remainder_toNat {r : UInt64} (d : UInt32) (hr : r.toNat < P) :
    (machineStep r d).2.toNat = (r.toNat * 2 ^ 32 + d.toNat) % P := by
  have hd : d.toNat < 2 ^ 32 := UInt32.toNat_lt d
  have hm : (r.toNat * B + d.toNat) % P < P := dividend_remainder_lt_P
  have hP32 : P < 2 ^ 32 := by norm_num [P]
  have hm32 : (r.toNat * B + d.toNat) % P < 2 ^ 32 := lt_trans hm hP32
  have hP64 : P < 2 ^ 64 := by norm_num [P]
  simp only [machineStep, UInt32.toNat_ofNat', UInt64.toNat_mod, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt hP64, machineWord_toNat d hr]
  have hm32' : (r.toNat * 2 ^ 32 + d.toNat) % P < 2 ^ 32 := by
    simpa [B] using hm32
  rw [Nat.mod_eq_of_lt hm32']

#print axioms packNat_of_lt
#print axioms packNat
#print axioms packNat_lt_two63
#print axioms modelExpr_lt_two63
#print axioms modelExpr_UInt64_roundtrip
#print axioms machineWord_toNat
#print axioms machineWord_lt_two63
#print axioms machineStep_quotient_toNat
#print axioms machineStep_remainder_toNat

end AspisR1.SamplerWord
