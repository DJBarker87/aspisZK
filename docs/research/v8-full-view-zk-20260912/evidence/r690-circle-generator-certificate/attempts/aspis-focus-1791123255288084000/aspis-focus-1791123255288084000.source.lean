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

lemma g_square : square g = s1 := by
  apply QuadraticAlgebra.ext
  · simp [square, g, s1]
    change ((4 - (1268011823 : ℤ) * 1268011823 : ℤ) : M) = ((7 : ℤ) : M)
    apply (ZMod.intCast_eq_intCast_iff _ _ P).2
    norm_num [P]
  · simp [square, g, s1]
    change (((2 : ℤ) * 1268011823 + 1268011823 * 2 : ℤ) : M) = ((777079998 : ℤ) : M)
    apply (ZMod.intCast_eq_intCast_iff _ _ P).2
    norm_num [P]

#print axioms g_square
end AspisV8R19.R690CircleGeneratorCertificate
