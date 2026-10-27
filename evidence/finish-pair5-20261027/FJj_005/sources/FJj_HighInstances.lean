import FJg_HighSum
import FJg_PartialSum
import FJg_LiteralTensor
import FJg_OriginalDigitValues
import FJd_HighReference
import FJg_TensorProduct
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_HighInstances
open scoped BigOperators

def shared {R : Type} [CommRing R] (f : Fin 64 → R) (c : Fin 16 → R) (h : Fin 4 → R) : R :=
  ∑ s : Fin 4,(∑ j : Fin 16,f ⟨16*s.val+j.val,by have := s.isLt;have := j.isLt;omega⟩*c j)*h s

theorem tower {K : Type} [Field K] (r u : K)
    [Fact (∀ x : K,x^2≠r+u*x)]
    (f : Fin 64 → QuadraticAlgebra K r u) (c : Fin 16 → QuadraticAlgebra K r u)
    (h : Fin 4 → QuadraticAlgebra K r u) :
    shared f c h=FJd_HighReference.shared f c h := rfl

def common {R : Type} [Mul R] (g : Fin 5 → Fin 4 → R) (j : Fin 16) : R :=
  g 2 ⟨j.val%4,Nat.mod_lt _ (by decide)⟩*g 3 ⟨j.val/4%4,Nat.mod_lt _ (by decide)⟩

theorem indices {R : Type} [Field R] (f : Fin 64 → R) (g : Fin 5 → Fin 4 → R) :
    FJd_HighReference.shared f (common g) (g 4)=∑ i : Fin 64,f i*FJg_TensorProduct.high g i := by
  rw [FJd_HighReference.value]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x=>f i*x)
  dsimp only [common,FJg_TensorProduct.high]
  have e0 : i.val%16%4=i.val%4 := by omega
  have e1 : i.val%16/4%4=i.val/4%4 := by omega
  simp only [e0,e1]
#print axioms tower
#print axioms indices
end AspisR1.FJj_HighInstances
end
