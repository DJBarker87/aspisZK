import InterleavedChordPair
import NaturalChordProjection

/-! Selected full chord pair, with every polynomial identity consumed from a
typed symbolic lemma before concrete natural coordinates are substituted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 80
set_option maxHeartbeats 2000
namespace AspisV8.InterleavedChordRows
noncomputable section
open Polynomial AspisV8.NaturalChordImage AspisV8.NaturalChordProjection
open AspisV8.ChordPolynomialImage AspisV8.InterleavedChordLinear
variable {K : Type*} [Field K] [NeZero (2 : K)] [DecidableEq K]

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- Fix the literal polynomial as `toFun` before selecting a concrete width. -/
def evenTransform (a b c : K) (A B : V →ₗ[K] K[X]) : V →ₗ[K] K[X] where
  toFun v := evenPart a b c (A v) (B v)
  map_add' v w := by
    simp only [← even_linear_formula]
    exact LinearMap.map_add _ v w
  map_smul' r v := by
    simp only [← even_linear_formula]
    exact LinearMap.map_smul _ r v
def oddTransform (a b c : K) (A B : V →ₗ[K] K[X]) : V →ₗ[K] K[X] where
  toFun v := oddPart a b c (A v) (B v)
  map_add' v w := by
    simp only [← odd_linear_formula]
    exact LinearMap.map_add _ v w
  map_smul' r v := by
    simp only [← odd_linear_formula]
    exact LinearMap.map_smul _ r v

theorem evenTransform_apply (a b c : K) (A B : V →ₗ[K] K[X]) (v : V) :
    evenTransform a b c A B v=evenPart a b c (A v) (B v) := rfl
theorem oddTransform_apply (a b c : K) (A B : V →ₗ[K] K[X]) (v : V) :
    oddTransform a b c A B v=oddPart a b c (A v) (B v) := rfl

def fullEvenLinear (a b c : K) : (Fin 1024 → K) →ₗ[K] K[X] :=
  evenTransform a b c evenPolynomial oddPolynomial
def fullOddLinear (a b c : K) : (Fin 1024 → K) →ₗ[K] K[X] :=
  oddTransform a b c evenPolynomial oddPolynomial

theorem fullEvenLinear_apply (a b c : K) (q : Fin 1024 → K) :
    fullEvenLinear a b c q=fullEven a b c q := by
  unfold fullEvenLinear fullEven
  rw [evenTransform_apply,evenPolynomial_apply,oddPolynomial_apply]
theorem fullOddLinear_apply (a b c : K) (q : Fin 1024 → K) :
    fullOddLinear a b c q=fullOdd a b c q := by
  unfold fullOddLinear fullOdd
  rw [oddTransform_apply,evenPolynomial_apply,oddPolynomial_apply]

#print axioms fullEvenLinear_apply
#print axioms fullOddLinear_apply
end
end AspisV8.InterleavedChordRows
