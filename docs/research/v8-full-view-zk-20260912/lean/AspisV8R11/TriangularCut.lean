import AspisV8H1C2.FiniteTransport
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Abel

set_option autoImplicit false
namespace AspisV8R11
noncomputable section
variable {A B U O : Type*} [AddCommGroup A] [AddCommGroup B]

def triangularCut (initialOffset : A) (laterOffset : A → B) :
    (A × B) ≃ (A × B) where
  toFun x := (x.1 + initialOffset, x.2 + laterOffset (x.1 + initialOffset))
  invFun y := (y.1 - initialOffset, y.2 - laterOffset y.1)
  left_inv x := by
    rcases x with ⟨a,b⟩
    simp
  right_inv y := by
    rcases y with ⟨a,b⟩
    simp

def firstCutEquiv (coordinates : U ≃ (A × B))
    (initialOffset : A) (laterOffset : A → B) : U ≃ (A × B) :=
  coordinates.trans (triangularCut initialOffset laterOffset)

theorem first_cut_uniform
    [Fintype U] [Nonempty U] [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (coordinates : U ≃ (A × B))
    (initialOffset : A) (laterOffset : A → B) :
    AspisV8H1C2.SameUniformLaw
      (firstCutEquiv coordinates initialOffset laterOffset)
      (fun y : A × B => y) := by
  exact AspisV8H1C2.sameUniformLaw_of_equiv _ _
    (firstCutEquiv coordinates initialOffset laterOffset) (fun _ => rfl)

def contextwiseFirstCut (coordinates : U ≃ (A × B))
    (initialOffset : O → A) (laterOffset : O → A → B) :
    (O × U) ≃ (O × (A × B)) where
  toFun x := (x.1, firstCutEquiv coordinates (initialOffset x.1)
    (laterOffset x.1) x.2)
  invFun y := (y.1, (firstCutEquiv coordinates (initialOffset y.1)
    (laterOffset y.1)).symm y.2)
  left_inv x := by
    rcases x with ⟨o,u⟩
    simp
  right_inv y := by
    rcases y with ⟨o,v⟩
    simp

def contextToTranscriptFiber (coordinates : U ≃ (A × B))
    (initialOffset : O → A) (laterOffset : O → A → B) (view : A × B) :
    O ≃ {x : O × U //
      firstCutEquiv coordinates (initialOffset x.1) (laterOffset x.1) x.2 = view} where
  toFun o := ⟨(o, (firstCutEquiv coordinates (initialOffset o)
    (laterOffset o)).symm view), by simp⟩
  invFun x := x.1.1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have h := congrArg
        (firstCutEquiv coordinates (initialOffset x.1.1) (laterOffset x.1.1)).symm x.2
      simpa using h.symm

#print axioms first_cut_uniform
#print axioms contextwiseFirstCut
#print axioms contextToTranscriptFiber
end
end AspisV8R11
