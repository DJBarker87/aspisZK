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
    (hre : (P : ℤ) ∣ c - (a * a - b * b))
    (him : (P : ℤ) ∣ d - (a * b + b * a)) :
    square (⟨(a : M), (b : M)⟩ : C) = ⟨(c : M), (d : M)⟩ := by
  apply QuadraticAlgebra.ext
  · simp [square]
    change ((a*a - b*b : ℤ) : M) = ((c : ℤ) : M)
    exact (ZMod.intCast_eq_intCast_iff _ _ P).2 hre
  · simp [square]
    change ((a*b + b*a : ℤ) : M) = ((d : ℤ) : M)
    exact (ZMod.intCast_eq_intCast_iff _ _ P).2 him

lemma g_square : square g = s1 := by
  simpa [g,s1] using square_int 2 1268011823 7 777079998 (by norm_num [P]) (by norm_num [P])

#print axioms g_square
end AspisV8R19.R690CircleGeneratorCertificate
