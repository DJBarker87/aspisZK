import SelectedMiddleFourAlpha
import Gamma29Reconstruction
import ComponentRows
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Tactic

/-! S4 UNCOMPILED finite-data composition. The algorithm reads disclosed
finals and public OOD data, not Q/p. The theorem states precisely which
per-node representation evidence is still required from the real collector.
Interpolation alone never establishes such evidence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
namespace AspisV8Completion.FSV8S4MatrixReconstruction
open Polynomial
open scoped BigOperators
open AspisV8.SelectedMiddleFourAlpha AspisV8.Gamma29Reconstruction
open AspisV8.ClaimTransport
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation AspisV5FriConcreteEncoderApplicability
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]
abbrev Tuple (K : Type*) := Fin 29 → Fin 1024 → K

/-- The same construction specified by the permitted-data access contract. -/
def quotientRows (alphaNodes : K → Finset K)
    (finals : K → K → Fin 256 → K) : K → Fin 1024 → K :=
  fun gamma => Generic.reconstruct (alphaNodes gamma) (finals gamma)

def reconstruct (gammaNodes : Finset K) (alphaNodes : K → Finset K)
    (finals : K → K → Fin 256 → K)
    (data : K → AspisV8.OODInterpolant.Data (K := K)) : Tuple K :=
  reconstructed gammaNodes (fun gamma =>
    AspisV8.ComponentRows.original (data gamma) (quotientRows alphaNodes finals gamma))

def componentPolynomial (p : Tuple K) (i : Fin 1024) : K[X] :=
  Polynomial.ofFn 29 (fun lane => p lane i)

theorem componentPolynomial_eval (p : Tuple K) (i : Fin 1024) (gamma : K) :
    (componentPolynomial p i).eval gamma = batch gamma p i := by
  unfold componentPolynomial
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    AspisV8.ClaimTransport.batch]
  change (∑ lane : Fin 29, p lane i * gamma ^ lane.val) =
    ∑ lane : Fin 29, gamma ^ lane.val * p lane i
  apply Finset.sum_congr rfl
  intro lane _
  ring

theorem componentPolynomial_degree (p : Tuple K) (i : Fin 1024) :
    (componentPolynomial p i).natDegree≤28 := by
  have h := Polynomial.ofFn_natDegree_lt (by decide : 1≤29) (fun lane => p lane i)
  change (componentPolynomial p i).natDegree<29 at h
  omega

/-- Equality at 29 DISTINCT gamma values determines all component columns. -/
theorem tuple_eq_of_29_batches (nodes : Finset K) (count : nodes.card=29)
    (p q : Tuple K) (same : ∀ gamma∈nodes, batch gamma p=batch gamma q) : p=q := by
  funext lane i
  let diff := componentPolynomial p i-componentPolynomial q i
  have degree : diff.natDegree≤28 :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le (componentPolynomial_degree p i) (componentPolynomial_degree q i))
  have zeros : ∀ gamma∈nodes, diff.eval gamma=0 := by
    intro gamma member
    rw [Polynomial.eval_sub,componentPolynomial_eval,componentPolynomial_eval,
      congrFun (same gamma member) i,sub_self]
  have zero := degree28_zero_of_29_nodes nodes count diff degree zeros
  have coeff := congrArg (fun poly : K[X] => poly.coeff lane.val) zero
  have coefficientZero : p lane i-q lane i=0 := by
    simpa only [diff,componentPolynomial,Polynomial.coeff_sub,
      Polynomial.ofFn_coeff_eq_val_of_lt (fun j => p j i) lane.isLt,
      Polynomial.ofFn_coeff_eq_val_of_lt (fun j => q j i) lane.isLt,
      Polynomial.coeff_zero] using coeff
  exact sub_eq_zero.mp coefficientZero

/-- Actual finals determine the common Q; the source representation property
is only used afterwards to identify the resulting original message. -/
theorem reconstructed_eq_common_tuple
    (gammaNodes : Finset K) (gammaCount : gammaNodes.card=29)
    (alphaNodes : K → Finset K)
    (alphaCount : ∀ g∈gammaNodes, (alphaNodes g).card=4)
    (finals : K → K → Fin 256 → K)
    (data : K → AspisV8.OODInterpolant.Data (K := K))
    (p : Tuple K)
    (represented : ∀ g∈gammaNodes, ∃ q : Fin 1024 → K,
      (∀ a∈alphaNodes g, finals g a=coefficientFoldLayer 256 a q) ∧
      AspisV8.ComponentRows.original (data g) q=batch g p) :
    reconstruct gammaNodes alphaNodes finals data=p := by
  apply tuple_eq_of_29_batches gammaNodes gammaCount
  intro gamma member
  unfold reconstruct
  rw [nodal_reconstruction gammaNodes _ gammaCount gamma member]
  obtain ⟨q,folds,original⟩ := represented gamma member
  have recovered : quotientRows alphaNodes finals gamma=q :=
    Generic.reconstruct_folds (alphaNodes gamma) (alphaCount gamma member)
      (finals gamma) q folds
  rw [recovered]
  exact original

/-- Family membership is a CONSEQUENCE of full nodal representation and the
same small family. The reconstruction function still has no family/p input.
This does not produce the 116 usable nodes or turn RecoveredHigh into an
executable acceptance predicate. -/
theorem reconstructed_member_of_single_family
    (gammaNodes : Finset K) (gammaCount : gammaNodes.card=29)
    (alphaNodes : K → Finset K)
    (alphaCount : ∀ g∈gammaNodes, (alphaNodes g).card=4)
    (finals : K → K → Fin 256 → K)
    (data : K → AspisV8.OODInterpolant.Data (K := K))
    (family : Finset (Tuple K)) (familyCap : family.card≤1)
    (nodesRecovered : ∀ g∈gammaNodes, ∃ q : Fin 1024 → K,
      (∀ a∈alphaNodes g, finals g a=coefficientFoldLayer 256 a q) ∧
      ∃ p∈family, AspisV8.ComponentRows.original (data g) q=batch g p) :
    reconstruct gammaNodes alphaNodes finals data∈family := by
  classical
  have nonempty : gammaNodes.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨g0,g0mem⟩ := nonempty
  obtain ⟨q0,f0,p0,p0mem,repr0⟩ := nodesRecovered g0 g0mem
  have allRepr : ∀ g∈gammaNodes, ∃ q : Fin 1024 → K,
      (∀ a∈alphaNodes g, finals g a=coefficientFoldLayer 256 a q) ∧
      AspisV8.ComponentRows.original (data g) q=batch g p0 := by
    intro g member
    obtain ⟨q,folds,p,pmem,repr⟩ := nodesRecovered g member
    have same : p=p0 := Finset.card_le_one.mp familyCap p pmem p0 p0mem
    exact ⟨q,folds,by simpa [same] using repr⟩
  rw [reconstructed_eq_common_tuple gammaNodes gammaCount alphaNodes alphaCount finals data p0 allRepr]
  exact p0mem

#print axioms tuple_eq_of_29_batches
#print axioms reconstructed_eq_common_tuple
#print axioms reconstructed_member_of_single_family
end
end AspisV8Completion.FSV8S4MatrixReconstruction
