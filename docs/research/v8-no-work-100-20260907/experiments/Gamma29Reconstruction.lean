import AspisFormal.K1.V7ExactCorrelatedAgreementReleasedLift
import ClaimTransport

/-! Reconstruct twenty-nine coefficient messages from twenty-nine distinct
actual original-message responses, using the pinned V7 released interpolation
constructor. The same nodal responses, when they satisfy the three literal
batched linear-functional equations, force all eighty-seven component claims.

This is finite deterministic algebra, not a forking, shared-support, low-degree
curve coverage, early-C1 membership, semantic-validity or payment theorem.
The responses may be selected after gamma and later challenges. No claim is
made that their interpolated tuple was fixed before those challenges.
V7 source pin: 26a9cd4718aae9f9de7ef1c3394fb74a229085d5.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.Gamma29Reconstruction
open Polynomial Finset
open AspisK1.V7ExactCorrelatedAgreementReleasedLift
open AspisV8.ClaimTransport
noncomputable section
variable {K : Type*} [Field K]

def reconstructed (nodes : Finset K) (candidate : K → Fin 1024 → K) :
    Fin 29 → Fin 1024 → K :=
  releasedInterpolationComponents (curveDegree := 28) nodes candidate

/-- Finset cardinality means twenty-nine distinct challenge values. The
output is an actual released coefficient message at every node, not merely
an ambient GRS polynomial. No received-word or support premise is needed. -/
theorem nodal_reconstruction (nodes : Finset K)
    (candidate : K → Fin 1024 → K) (count : nodes.card = 29)
    (gamma : K) (member : gamma ∈ nodes) :
    batch gamma (reconstructed nodes candidate) = candidate gamma := by
  exact releasedInterpolationComponents_curve_eq_candidate
    (curveDegree := 28) nodes candidate count gamma member

/-- A named small root argument, with no enumeration of a concrete field. -/
theorem degree28_zero_of_29_nodes (nodes : Finset K) (count : nodes.card = 29)
    (poly : K[X]) (degree : poly.natDegree ≤ 28)
    (zeros : ∀ gamma ∈ nodes, poly.eval gamma = 0) : poly = 0 := by
  classical
  by_contra nonzero
  have subset : nodes.val ⊆ poly.roots := by
    intro gamma member
    exact (Polynomial.mem_roots nonzero).mpr (zeros gamma member)
  have bound : nodes.card ≤ 28 :=
    (Polynomial.card_le_degree_of_subset_roots subset).trans degree
  omega

/-- Source-neutral ClaimTransport endpoint: the same fixed claims and
functionals occur at every node, and all three equations are required there.
An averaged kappa equation or a single scalar prior is not this hypothesis. -/
theorem claims_exact_of_nodal_batches (nodes : Finset K) (count : nodes.card = 29)
    (components : Fin 29 → Fin 1024 → K)
    (rows : Fin 3 → (Fin 1024 → K) →ₗ[K] K) (claimed : Fin 3 → Fin 29 → K)
    (matched : ∀ gamma ∈ nodes, ∀ row : Fin 3,
      rows row (batch gamma components) =
        ∑ lane : Fin 29, gamma ^ lane.val * claimed row lane) :
    ∀ row lane, claimed row lane = rows row (components lane) := by
  intro row lane
  have zero : errorPolynomial (rows row) components (claimed row) = 0 :=
    degree28_zero_of_29_nodes nodes count _
      (component_error_degree (rows row) components (claimed row)) (by
        intro gamma member
        rw [← component_error_eval, matched gamma member row, sub_self])
  have coefficient := component_error_coeff (rows row) components (claimed row) lane
  rw [zero, Polynomial.coeff_zero] at coefficient
  exact sub_eq_zero.mp coefficient.symm

/-- The tuple is constructed from the actual responses, rather than supplied
with a desired batching equation. This recovers precisely the eighty-seven
linear claims; shared support and all payment residuals remain downstream. -/
theorem reconstructed_claims_exact (nodes : Finset K) (count : nodes.card = 29)
    (candidate : K → Fin 1024 → K)
    (rows : Fin 3 → (Fin 1024 → K) →ₗ[K] K) (claimed : Fin 3 → Fin 29 → K)
    (matched : ∀ gamma ∈ nodes, ∀ row : Fin 3,
      rows row (candidate gamma) =
        ∑ lane : Fin 29, gamma ^ lane.val * claimed row lane) :
    ∀ row lane, claimed row lane = rows row (reconstructed nodes candidate lane) := by
  apply claims_exact_of_nodal_batches nodes count (reconstructed nodes candidate) rows claimed
  intro gamma member row
  rw [nodal_reconstruction nodes candidate count gamma member]
  exact matched gamma member row

#print axioms nodal_reconstruction
#print axioms degree28_zero_of_29_nodes
#print axioms claims_exact_of_nodal_batches
#print axioms reconstructed_claims_exact
end
end AspisV8.Gamma29Reconstruction
