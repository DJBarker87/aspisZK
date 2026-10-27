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
  unfold pack base
  rw [FJf_EbyKPush.mul_scalar]
  apply QuadraticAlgebra.ext
  · change _=(⟨⟨a 0,a 1⟩,⟨a 2,a 3⟩⟩ : FJf_RawTower.Q)*⟨⟨s,0⟩,0⟩
    rw [FJf_EbyKPush.mul_scalar,FJf_EbyKPush.mul_scalar,FJf_EbyKPush.mul_scalar]
  · change _=(⟨⟨a 4,a 5⟩,⟨a 6,a 7⟩⟩ : FJf_RawTower.Q)*⟨⟨s,0⟩,0⟩
    rw [FJf_EbyKPush.mul_scalar,FJf_EbyKPush.mul_scalar,FJf_EbyKPush.mul_scalar]
#print axioms add
#print axioms zero
#print axioms scalar
end AspisR1.FJi_WidePack
end
