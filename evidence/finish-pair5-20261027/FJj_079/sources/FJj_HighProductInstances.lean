import FJg_TensorProduct
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_HighProductInstances

def product {R : Type} [CommRing R] (g : Fin 5 → Fin 4 → R) (i : Fin 64) : R :=
  g 2 ⟨i.val%4,Nat.mod_lt _ (by decide)⟩*
  g 3 ⟨i.val/4%4,Nat.mod_lt _ (by decide)⟩*
  g 4 ⟨i.val/16,by have := i.isLt;omega⟩

theorem tower {K : Type} [Field K] (r u : K)
    [Fact (∀ x : K,x^2≠r+u*x)]
    (g : Fin 5 → Fin 4 → QuadraticAlgebra K r u) (i : Fin 64) :
    product g i=FJg_TensorProduct.high g i := rfl

theorem map {R S : Type} [Field R] [Field S] (φ : R →+* S)
    (g : Fin 5 → Fin 4 → R) (i : Fin 64) :
    φ (FJg_TensorProduct.high g i)=FJg_TensorProduct.high (fun d s=>φ (g d s)) i := by
  unfold FJg_TensorProduct.high
  rw [map_mul,map_mul]
#print axioms tower
#print axioms map
end AspisR1.FJj_HighProductInstances
end
