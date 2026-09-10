import QuadraticFamilyAssembly
import QuadraticSourceSharp
import QuadraticSelectedDegree

/-! Fixed C1/C2 quadratic factor cover, before either OOD point.
No retained/OOD-dependent family replaces the fixed prime-factor family.
This covers literal quadratic factor roots, not all accepted executions.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedQuadraticCover
noncomputable section
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisV8.SelectedReceivedOracle AspisV8.SelectedOODGate
open AspisV8.SelectedFactorCoherence
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap' AspisV5ComponentCQM31TowerExact.M31Exact
    (A := K) 2147483647
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P
attribute [local irreducible] curvePrimeFactors

private theorem filtered_weight_le {I : Type*} (s : Multiset I)
    (predicate : I → Prop) [DecidablePred predicate] (weight : I → Nat) :
    ((s.filter predicate).map weight).sum ≤ (s.map weight).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      by_cases h : predicate a
      · simpa only [Multiset.filter_cons_of_pos s h, Multiset.map_cons, Multiset.sum_cons]
          using Nat.add_le_add_left ih (weight a)
      · simpa only [Multiset.filter_cons_of_neg s h, Multiset.map_cons, Multiset.sum_cons]
          using ih.trans (Nat.le_add_left _ _)

def factors (c1 : C1Received) (c2 : C2Received) : Multiset (TrivariatePolynomial K) :=
  (curvePrimeFactors (parent c1 c2)).filter (fun F => F.natDegree = 2)

theorem fixed_cover (c1 : C1Received) (c2 : C2Received) :
    ∃ E : K[X], ∃ exceptional : Finset K,
      E ≠ 0 ∧ E.natDegree ≤ 114687 ∧ exceptional.card ≤ 936616 ∧
      ∀ (points : Fin 2 → K) (answers : Fin 2 → K[X]) gamma (U : K[X]),
        (∃ F ∈ curvePrimeFactors (parent c1 c2), F.natDegree = 2 ∧
          (∀ r, FactorCoherence.pointSubstitution (points r) (answers r) F = 0) ∧
          challengeCandidateHom gamma U F = 0) →
        (∀ r, E.eval (points r) = 0) ∨ gamma ∈ exceptional := by
  classical
  let xw := fun F : TrivariatePolynomial K => (trivariateXOuterEquiv K F).natDegree
  let gw := fun F : TrivariatePolynomial K => 8*trivariateYZWeight 28 F
  have nonzero : parent c1 c2 ≠ 0 :=
    curveTrivariatePolynomial_ne_zero _ (fixedInterpolant_nonzero c1 c2)
  have alternatives : ∀ F ∈ factors c1 c2,
      (∃ E : K[X], E ≠ 0 ∧ E.natDegree ≤ xw F ∧
        ∀ (points : Fin 2 → K) (answers : Fin 2 → K[X]),
          (∀ r, FactorCoherence.pointSubstitution (points r) (answers r) F = 0) →
          ∀ r, E.eval (points r) = 0) ∨
      (∀ G : Finset K,
        (∀ gamma ∈ G, ∃ U : K[X], challengeCandidateHom gamma U F = 0) →
        G.card ≤ gw F) := by
    intro F member
    obtain ⟨original, degree⟩ := Multiset.mem_filter.mp member
    have irreducible := (curvePrimeFactors_prime (parent c1 c2) nonzero F original).irreducible
    have small := QuadraticSelectedDegree.selected_discriminant_lt_characteristic c1 c2 F original
    rcases QuadraticSourceSharp.fixed_source_alternative 2147483647 28 F irreducible degree small with
      obstruction | sparse
    · obtain ⟨E, en, ed, forces⟩ := obstruction
      have dx := QuadraticSelectedDegree.discriminant_x_degree_le F
      exact Or.inl ⟨E, en, by dsimp [xw]; omega, forces⟩
    · exact Or.inr sparse
  obtain ⟨E, exceptional, en, ed, ec, covers⟩ := QuadraticFamilyAssembly.assemble
    (factors c1 c2) xw gw
    (fun F points answers => ∀ r, FactorCoherence.pointSubstitution (points r) (answers r) F = 0)
    (fun F gamma => ∃ U : K[X], challengeCandidateHom gamma U F = 0) alternatives
  refine ⟨E, exceptional, en, ?_, ?_, ?_⟩
  · have filtered := filtered_weight_le (curvePrimeFactors (parent c1 c2))
      (fun F => F.natDegree = 2) xw
    exact ed.trans (filtered.trans ((MonicFactorOOD.all_factor_x_degrees_le _ nonzero).trans
      (SelectedMonicCover.parent_x_degree c1 c2)))
  · have filtered := filtered_weight_le (curvePrimeFactors (parent c1 c2))
      (fun F => F.natDegree = 2) gw
    have total := FactorIdentityCover.all_factor_weights_le 28 (parent c1 c2) nonzero
    have parentWeight := trivariateYZWeight_curveTrivariatePolynomial_lt
      (by norm_num : 0 < 117078) (fixedInterpolant c1 c2)
    change trivariateYZWeight 28 (parent c1 c2) < 117078 at parentWeight
    have scale : ((curvePrimeFactors (parent c1 c2)).map gw).sum =
        8*((curvePrimeFactors (parent c1 c2)).map (trivariateYZWeight 28)).sum := by
      dsimp [gw]
      generalize curvePrimeFactors (parent c1 c2) = s
      induction s using Multiset.induction_on with
      | empty => simp
      | @cons F rest ih =>
          simp only [Multiset.map_cons, Multiset.sum_cons]
          rw [ih]
          omega
    have bound := ec.trans filtered
    rw [scale] at bound
    omega
  · intro points answers gamma U witness
    obtain ⟨F, member, degree, identities, root⟩ := witness
    exact covers points answers gamma ⟨F, Multiset.mem_filter.mpr ⟨member, degree⟩,
      identities, U, root⟩

#print axioms filtered_weight_le
#print axioms fixed_cover
end
end AspisV8.SelectedQuadraticCover
