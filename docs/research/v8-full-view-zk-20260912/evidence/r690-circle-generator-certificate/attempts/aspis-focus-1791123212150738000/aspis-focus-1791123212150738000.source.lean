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
  apply QuadraticAlgebra.ext <;>
    simp [square, g, s1, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> norm_num [P]

#print axioms g_square
end AspisV8R19.R690CircleGeneratorCertificate
