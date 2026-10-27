import FJf_EbyKPush
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_WidePack
open Aeneas Aeneas.Std Result
abbrev F := ZMod 2147483647
abbrev E := AspisWideTower.WideExact
def pack (v : Fin 8 → F) : E :=
  ⟨⟨⟨v 0,v 1⟩,⟨v 2,v 3⟩⟩,⟨⟨v 4,v 5⟩,⟨v 6,v 7⟩⟩⟩
def base (s : F) : E := ⟨⟨⟨s,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨0,0⟩⟩⟩
theorem add (a b : Fin 8 → F) : pack (fun j=>a j+b j)=pack a+pack b := rfl
theorem zero : pack (fun _=>0)=0 := rfl
theorem scalar (a : Fin 8 → F) (s : F) : pack (fun j=>a j*s)=pack a*base s := by
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
    simp only [pack,base,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero,
      mul_zero,zero_mul,add_zero,zero_add]
#print axioms add
#print axioms zero
#print axioms scalar
end AspisR1.FJi_WidePack
end
