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

lemma g_square : square g = s1 := by
  simpa [g,s1] using square_int 2 1268011823 7 777079998
    (by norm_num [Int.ModEq, P]) (by norm_num [Int.ModEq, P])

#print axioms g_square
end AspisV8R19.R690CircleGeneratorCertificate
