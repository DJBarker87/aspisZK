import AspisV8R15.ExactTowerBase
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R690CircleGeneratorCertificate
open AspisV8R15.ExactTowerBase

abbrev M := M31Exact
abbrev C := CM31Exact

def square (z : C) : C := z * z

def g : C := ⟨(2 : M), (1268011823 : M)⟩
def s1 : C := ⟨(7 : M), (777079998 : M)⟩
def s2 : C := ⟨(97 : M), (141701737 : M)⟩
def s3 : C := ⟨(18817 : M), (1720333214 : M)⟩
def s4 : C := ⟨(708158977 : M), (683185920 : M)⟩
def s5 : C := ⟨(334835419 : M), (1444967316 : M)⟩
def s6 : C := ⟨(2042371533 : M), (1362265296 : M)⟩
def s7 : C := ⟨(212706801 : M), (1223819887 : M)⟩
def s8 : C := ⟨(421007138 : M), (256177860 : M)⟩
def s9 : C := ⟨(6346213 : M), (905523693 : M)⟩
def s10 : C := ⟨(1022251061 : M), (788094511 : M)⟩
def s11 : C := ⟨(1633461177 : M), (574296567 : M)⟩
def s12 : C := ⟨(595037635 : M), (2111542451 : M)⟩
def s13 : C := ⟨(1799120754 : M), (343598868 : M)⟩
def s14 : C := ⟨(438833264 : M), (1327019128 : M)⟩
def s15 : C := ⟨(1389168750 : M), (838891026 : M)⟩
def s16 : C := ⟨(1543902459 : M), (1632329423 : M)⟩
def s17 : C := ⟨(1330239767 : M), (1446369578 : M)⟩
def s18 : C := ⟨(1420207432 : M), (2023238517 : M)⟩
def s19 : C := ⟨(2015554631 : M), (1088093947 : M)⟩
def s20 : C := ⟨(996212859 : M), (1140996376 : M)⟩
def s21 : C := ⟨(1434706457 : M), (1835793811 : M)⟩
def s22 : C := ⟨(13610297 : M), (1064696601 : M)⟩
def s23 : C := ⟨(785043271 : M), (1260750973 : M)⟩
def s24 : C := ⟨(838195206 : M), (1774253895 : M)⟩
def s25 : C := ⟨(579625837 : M), (1690787918 : M)⟩
def s26 : C := ⟨(1179735656 : M), (1241207368 : M)⟩
def s27 : C := ⟨(590768354 : M), (978592373 : M)⟩
def s28 : C := ⟨(32768 : M), (2147450879 : M)⟩
def s29 : C := ⟨(0 : M), (2147483646 : M)⟩
def s30 : C := ⟨(2147483646 : M), (0 : M)⟩
def s31 : C := ⟨(1 : M), (0 : M)⟩

lemma square_int (a b c d : ℤ)
    (hre : Int.ModEq (P : ℤ) (a * a + -(b * b)) c)
    (him : Int.ModEq (P : ℤ) (a * b + b * a) d) :
    square (⟨(a : M), (b : M)⟩ : C) = ⟨(c : M), (d : M)⟩ := by
  apply QuadraticAlgebra.ext
  · simp [square]
    rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_neg, ← Int.cast_add]
    exact (ZMod.intCast_eq_intCast_iff _ _ P).2 hre
  · simp [square]
    rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_add]
    exact (ZMod.intCast_eq_intCast_iff _ _ P).2 him

lemma square_0 : square g = s1 := by
  simpa [g, s1] using square_int 2 1268011823 7 777079998
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_1 : square s1 = s2 := by
  simpa [s1, s2] using square_int 7 777079998 97 141701737
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_2 : square s2 = s3 := by
  simpa [s2, s3] using square_int 97 141701737 18817 1720333214
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_3 : square s3 = s4 := by
  simpa [s3, s4] using square_int 18817 1720333214 708158977 683185920
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_4 : square s4 = s5 := by
  simpa [s4, s5] using square_int 708158977 683185920 334835419 1444967316
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_5 : square s5 = s6 := by
  simpa [s5, s6] using square_int 334835419 1444967316 2042371533 1362265296
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_6 : square s6 = s7 := by
  simpa [s6, s7] using square_int 2042371533 1362265296 212706801 1223819887
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_7 : square s7 = s8 := by
  simpa [s7, s8] using square_int 212706801 1223819887 421007138 256177860
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_8 : square s8 = s9 := by
  simpa [s8, s9] using square_int 421007138 256177860 6346213 905523693
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_9 : square s9 = s10 := by
  simpa [s9, s10] using square_int 6346213 905523693 1022251061 788094511
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_10 : square s10 = s11 := by
  simpa [s10, s11] using square_int 1022251061 788094511 1633461177 574296567
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_11 : square s11 = s12 := by
  simpa [s11, s12] using square_int 1633461177 574296567 595037635 2111542451
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_12 : square s12 = s13 := by
  simpa [s12, s13] using square_int 595037635 2111542451 1799120754 343598868
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_13 : square s13 = s14 := by
  simpa [s13, s14] using square_int 1799120754 343598868 438833264 1327019128
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_14 : square s14 = s15 := by
  simpa [s14, s15] using square_int 438833264 1327019128 1389168750 838891026
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_15 : square s15 = s16 := by
  simpa [s15, s16] using square_int 1389168750 838891026 1543902459 1632329423
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_16 : square s16 = s17 := by
  simpa [s16, s17] using square_int 1543902459 1632329423 1330239767 1446369578
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_17 : square s17 = s18 := by
  simpa [s17, s18] using square_int 1330239767 1446369578 1420207432 2023238517
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_18 : square s18 = s19 := by
  simpa [s18, s19] using square_int 1420207432 2023238517 2015554631 1088093947
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_19 : square s19 = s20 := by
  simpa [s19, s20] using square_int 2015554631 1088093947 996212859 1140996376
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_20 : square s20 = s21 := by
  simpa [s20, s21] using square_int 996212859 1140996376 1434706457 1835793811
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_21 : square s21 = s22 := by
  simpa [s21, s22] using square_int 1434706457 1835793811 13610297 1064696601
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_22 : square s22 = s23 := by
  simpa [s22, s23] using square_int 13610297 1064696601 785043271 1260750973
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_23 : square s23 = s24 := by
  simpa [s23, s24] using square_int 785043271 1260750973 838195206 1774253895
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_24 : square s24 = s25 := by
  simpa [s24, s25] using square_int 838195206 1774253895 579625837 1690787918
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_25 : square s25 = s26 := by
  simpa [s25, s26] using square_int 579625837 1690787918 1179735656 1241207368
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_26 : square s26 = s27 := by
  simpa [s26, s27] using square_int 1179735656 1241207368 590768354 978592373
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_27 : square s27 = s28 := by
  simpa [s27, s28] using square_int 590768354 978592373 32768 2147450879
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_28 : square s28 = s29 := by
  simpa [s28, s29] using square_int 32768 2147450879 0 2147483646
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_29 : square s29 = s30 := by
  simpa [s29, s30] using square_int 0 2147483646 2147483646 0
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

lemma square_30 : square s30 = s31 := by
  simpa [s30, s31] using square_int 2147483646 0 1 0
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

theorem square_iterate_pow (x : C) (k : Nat) :
    square^[k] x = x ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      unfold square
      calc
        x ^ 2 ^ n * x ^ 2 ^ n = x ^ (2 ^ n + 2 ^ n) := by rw [pow_add]
        _ = x ^ (2 ^ (n + 1)) := by
          congr 1
          rw [pow_succ]
          ring

lemma iterate_0 : square^[0] g = g := rfl
lemma iterate_1 : square^[1] g = s1 := by
  rw [Function.iterate_succ_apply', iterate_0]
  exact square_0

lemma iterate_2 : square^[2] g = s2 := by
  rw [Function.iterate_succ_apply', iterate_1]
  exact square_1

lemma iterate_3 : square^[3] g = s3 := by
  rw [Function.iterate_succ_apply', iterate_2]
  exact square_2

lemma iterate_4 : square^[4] g = s4 := by
  rw [Function.iterate_succ_apply', iterate_3]
  exact square_3

lemma iterate_5 : square^[5] g = s5 := by
  rw [Function.iterate_succ_apply', iterate_4]
  exact square_4

lemma iterate_6 : square^[6] g = s6 := by
  rw [Function.iterate_succ_apply', iterate_5]
  exact square_5

lemma iterate_7 : square^[7] g = s7 := by
  rw [Function.iterate_succ_apply', iterate_6]
  exact square_6

lemma iterate_8 : square^[8] g = s8 := by
  rw [Function.iterate_succ_apply', iterate_7]
  exact square_7

lemma iterate_9 : square^[9] g = s9 := by
  rw [Function.iterate_succ_apply', iterate_8]
  exact square_8

lemma iterate_10 : square^[10] g = s10 := by
  rw [Function.iterate_succ_apply', iterate_9]
  exact square_9

lemma iterate_11 : square^[11] g = s11 := by
  rw [Function.iterate_succ_apply', iterate_10]
  exact square_10

lemma iterate_12 : square^[12] g = s12 := by
  rw [Function.iterate_succ_apply', iterate_11]
  exact square_11

lemma iterate_13 : square^[13] g = s13 := by
  rw [Function.iterate_succ_apply', iterate_12]
  exact square_12

lemma iterate_14 : square^[14] g = s14 := by
  rw [Function.iterate_succ_apply', iterate_13]
  exact square_13

lemma iterate_15 : square^[15] g = s15 := by
  rw [Function.iterate_succ_apply', iterate_14]
  exact square_14

lemma iterate_16 : square^[16] g = s16 := by
  rw [Function.iterate_succ_apply', iterate_15]
  exact square_15

lemma iterate_17 : square^[17] g = s17 := by
  rw [Function.iterate_succ_apply', iterate_16]
  exact square_16

lemma iterate_18 : square^[18] g = s18 := by
  rw [Function.iterate_succ_apply', iterate_17]
  exact square_17

lemma iterate_19 : square^[19] g = s19 := by
  rw [Function.iterate_succ_apply', iterate_18]
  exact square_18

lemma iterate_20 : square^[20] g = s20 := by
  rw [Function.iterate_succ_apply', iterate_19]
  exact square_19

lemma iterate_21 : square^[21] g = s21 := by
  rw [Function.iterate_succ_apply', iterate_20]
  exact square_20

lemma iterate_22 : square^[22] g = s22 := by
  rw [Function.iterate_succ_apply', iterate_21]
  exact square_21

lemma iterate_23 : square^[23] g = s23 := by
  rw [Function.iterate_succ_apply', iterate_22]
  exact square_22

lemma iterate_24 : square^[24] g = s24 := by
  rw [Function.iterate_succ_apply', iterate_23]
  exact square_23

lemma iterate_25 : square^[25] g = s25 := by
  rw [Function.iterate_succ_apply', iterate_24]
  exact square_24

lemma iterate_26 : square^[26] g = s26 := by
  rw [Function.iterate_succ_apply', iterate_25]
  exact square_25

lemma iterate_27 : square^[27] g = s27 := by
  rw [Function.iterate_succ_apply', iterate_26]
  exact square_26

lemma iterate_28 : square^[28] g = s28 := by
  rw [Function.iterate_succ_apply', iterate_27]
  exact square_27

lemma iterate_29 : square^[29] g = s29 := by
  rw [Function.iterate_succ_apply', iterate_28]
  exact square_28

lemma iterate_30 : square^[30] g = s30 := by
  rw [Function.iterate_succ_apply', iterate_29]
  exact square_29

lemma iterate_31 : square^[31] g = s31 := by
  rw [Function.iterate_succ_apply', iterate_30]
  exact square_30


theorem g_pow_two_pow_30 : g ^ (2 ^ 30) = (-1 : C) := by
  rw [← square_iterate_pow, iterate_30]
  apply QuadraticAlgebra.ext <;> norm_num [s30, P]

theorem g_pow_two_pow_31 : g ^ (2 ^ 31) = (1 : C) := by
  rw [← square_iterate_pow, iterate_31]
  apply QuadraticAlgebra.ext <;> norm_num [s31, P]

theorem g_norm_one : QuadraticAlgebra.norm g = (1 : M) := by
  simp [g, QuadraticAlgebra.norm_def]
  change ((4 + (1268011823 : ℤ) * 1268011823 : ℤ) : M) = ((1 : ℤ) : M)
  apply (ZMod.intCast_eq_intCast_iff _ _ P).2
  norm_num [Int.ModEq, P]

#print axioms square_iterate_pow
#print axioms g_pow_two_pow_30
#print axioms g_pow_two_pow_31
#print axioms g_norm_one
end AspisV8R19.R690CircleGeneratorCertificate
