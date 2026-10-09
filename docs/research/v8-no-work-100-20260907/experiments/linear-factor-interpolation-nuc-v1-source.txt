import PolynomialValueInterpolation
import Mathlib.RingTheory.Localization.FractionRing

/-! A bounded class of retained linear factors A(X,Z)Y+B(X,Z).
The fixed rational root is ASSUMED to be a polynomial in Z over K(X), of
bounded Z degree. This class is not asserted to contain every retained factor.
Regular good challenges are defined geometrically, without a provider:
there exists a polynomial U in the chosen code submodule, of bounded X degree,
and A_gamma != 0 with A_gamma*U+B_gamma=0. More than c such challenges construct
one c+1-component code curve. Degenerate A_gamma=0 is explicitly excluded.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.LinearFactorInterpolation
open Polynomial Finset
open AspisV8.PolynomialValueInterpolation
noncomputable section
variable {K L : Type*} [Field K] [Field L] [DecidableEq K]

def LinearRoot (A B : Polynomial K[X]) (gamma : K) (U : K[X]) : Prop :=
  A.eval (C gamma) * U + B.eval (C gamma) = 0

def Good (S : Submodule K K[X]) (D : Nat)
    (A B : Polynomial K[X]) (gamma : K) : Prop :=
  A.eval (C gamma) ≠ 0 ∧
    ∃ U : K[X], U ∈ S ∧ U.natDegree ≤ D ∧ LinearRoot A B gamma U

def goodSet (S : Submodule K K[X]) (D : Nat)
    (A B : Polynomial K[X]) (Gamma : Finset K) : Finset K := by
  classical
  exact Gamma.filter (Good S D A B)

theorem map_eval_constant (phi : K[X] →+* L)
    (A : Polynomial K[X]) (gamma : K) :
    (A.map phi).eval (scalarMap phi gamma) = phi (A.eval (C gamma)) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply phi (C gamma)

/-- Specialization derives the value equality used for interpolation.
The A_gamma nonzero premise is essential, not a totalized division hint. -/
theorem regular_root_value (phi : K[X] →+* L) (injective : Function.Injective phi)
    (A B : Polynomial K[X]) (R : L[X])
    (equation : A.map phi * R + B.map phi = 0)
    (gamma : K) (U : K[X]) (regular : A.eval (C gamma) ≠ 0)
    (root : LinearRoot A B gamma U) :
    R.eval (scalarMap phi gamma) = phi U := by
  have specialized := congrArg (fun P : L[X] => P.eval (scalarMap phi gamma)) equation
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_zero,
    map_eval_constant, map_eval_constant] at specialized
  have mapped := congrArg phi root
  change phi (A.eval (C gamma) * U + B.eval (C gamma)) = phi 0 at mapped
  rw [map_add, map_mul, map_zero] at mapped
  have leadingNonzero : phi (A.eval (C gamma)) ≠ 0 := by
    intro zero
    apply regular
    exact injective (zero.trans (map_zero phi).symm)
  apply mul_left_cancel₀ leadingNonzero
  exact add_right_cancel (specialized.trans mapped.symm)

/-- No candidate tuple is supplied. Dense geometric good challenges choose
the interpolation nodes and values from the fixed equation itself. The
resulting components remain in any supplied code submodule S. -/
theorem interpolation_dichotomy
    (phi : K[X] →+* L) (injective : Function.Injective phi)
    (A B : Polynomial K[X]) (R : L[X])
    (c D : Nat) (rootDegree : R.natDegree ≤ c)
    (equation : A.map phi * R + B.map phi = 0)
    (S : Submodule K K[X]) (Gamma : Finset K) :
    (goodSet S D A B Gamma).card ≤ c ∨
      ∃ p : Fin (c+1) → K[X],
        (∀ j, p j ∈ S ∧ (p j).natDegree ≤ D ∧ R.coeff j.val = phi (p j)) ∧
        ∀ gamma (U : K[X]), A.eval (C gamma) ≠ 0 → LinearRoot A B gamma U →
          U = ∑ j : Fin (c+1), gamma^j.val • p j := by
  classical
  by_cases sparse : (goodSet S D A B Gamma).card ≤ c
  · exact Or.inl sparse
  · right
    obtain ⟨nodes, subset, cardinality⟩ := Finset.exists_subset_card_eq
      (s := goodSet S D A B Gamma) (n := c+1) (by omega)
    let values : K → K[X] := fun gamma =>
      if good : Good S D A B gamma then Classical.choose good.2 else 0
    have nodeGood : ∀ node ∈ nodes, Good S D A B node := by
      intro node member
      exact (Finset.mem_filter.mp (subset member)).2
    have valuesGood : ∀ node ∈ nodes,
        values node ∈ S ∧ (values node).natDegree ≤ D ∧ LinearRoot A B node (values node) := by
      intro node member
      have good := nodeGood node member
      simp only [values, dif_pos good]
      exact Classical.choose_spec good.2
    have matched : ∀ node ∈ nodes,
        R.eval (scalarMap phi node) = phi (values node) := by
      intro node member
      exact regular_root_value phi injective A B R equation node (values node)
        (nodeGood node member).1 (valuesGood node member).2.2
    let p : Fin (c+1) → K[X] := fun j => component nodes values j.val
    refine ⟨p, ?_, ?_⟩
    · intro j
      exact ⟨component_mem S nodes values j.val (fun node member => (valuesGood node member).1),
        component_degree nodes values D j.val (fun node member => (valuesGood node member).2.1),
        coefficient_descent phi R c rootDegree nodes cardinality values matched j.val⟩
    · intro gamma U regular root
      exact candidate_eq_batch phi injective R c rootDegree nodes cardinality values matched
        gamma U (regular_root_value phi injective A B R equation gamma U regular root)

/-- Exact function field K(X), with the actual injection of polynomial
messages. A polynomial-in-gamma rational root of degree <=28 is a class
premise; the theorem does not derive it from two OOD identities. -/
theorem rational_29_dichotomy
    (A B : Polynomial K[X]) (R : Polynomial (FractionRing K[X]))
    (rootDegree : R.natDegree ≤ 28)
    (equation : A.map (algebraMap K[X] (FractionRing K[X])) * R +
      B.map (algebraMap K[X] (FractionRing K[X])) = 0)
    (S : Submodule K K[X]) (Gamma : Finset K) :
    (goodSet S 1024 A B Gamma).card ≤ 28 ∨
      ∃ p : Fin 29 → K[X],
        (∀ j, p j ∈ S ∧ (p j).natDegree ≤ 1024 ∧
          R.coeff j.val = algebraMap K[X] (FractionRing K[X]) (p j)) ∧
        ∀ gamma (U : K[X]), A.eval (C gamma) ≠ 0 → LinearRoot A B gamma U →
          U = ∑ j : Fin 29, gamma^j.val • p j :=
  interpolation_dichotomy (algebraMap K[X] (FractionRing K[X]))
    (IsFractionRing.injective K[X] (FractionRing K[X])) A B R 28 1024 rootDegree equation S Gamma

#print axioms map_eval_constant
#print axioms regular_root_value
#print axioms interpolation_dichotomy
#print axioms rational_29_dichotomy
end
end AspisV8.LinearFactorInterpolation
