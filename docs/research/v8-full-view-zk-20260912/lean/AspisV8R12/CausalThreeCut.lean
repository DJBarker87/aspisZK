import AspisV8H1C2.FiniteTransport
import Mathlib.Data.Fintype.Prod
set_option autoImplicit false
namespace AspisV8R12
noncomputable section
variable {A B C Z : Type*}
def causalThreeCut (first : A ≃ A) (second : A → B ≃ B) (third : A → B → C ≃ C) :
    (A × B × C) ≃ (A × B × C) where
  toFun x := let a := first x.1; let b := second a x.2.1; (a, b, third a b x.2.2)
  invFun y := (first.symm y.1, (second y.1).symm y.2.1, (third y.1 y.2.1).symm y.2.2)
  left_inv x := by rcases x with ⟨a,b,c⟩; simp
  right_inv x := by rcases x with ⟨a,b,c⟩; simp
def contextualThreeCut (e : Z → (A × B × C) ≃ (A × B × C)) :
    (Z × (A × B × C)) ≃ (Z × (A × B × C)) where
  toFun x := (x.1, e x.1 x.2)
  invFun y := (y.1, (e y.1).symm y.2)
  left_inv x := by rcases x with ⟨z,u⟩; simp
  right_inv y := by rcases y with ⟨z,u⟩; simp
theorem causal_three_cut_uniform [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (first : A ≃ A) (second : A → B ≃ B) (third : A → B → C ≃ C) :
    AspisV8H1C2.SameUniformLaw (causalThreeCut first second third) (fun y : A × B × C => y) := by
  exact AspisV8H1C2.sameUniformLaw_of_equiv _ _ (causalThreeCut first second third) (fun _ => rfl)
def complementToFiber (e : Z → (A × B × C) ≃ (A × B × C)) (view : A × B × C) :
    Z ≃ {x : Z × (A × B × C) // e x.1 x.2 = view} where
  toFun z := ⟨(z,(e z).symm view), by simp⟩
  invFun x := x.1.1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext; apply Prod.ext
    · rfl
    · have h := congrArg (e x.1.1).symm x.2; simpa using h.symm
#print axioms causalThreeCut
#print axioms contextualThreeCut
#print axioms causal_three_cut_uniform
#print axioms complementToFiber
end
end AspisV8R12
