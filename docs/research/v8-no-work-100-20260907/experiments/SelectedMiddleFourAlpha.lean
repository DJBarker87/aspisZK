import SelectedMiddleUniqueness
import ExactFoldRecovery

/-! Four disclosed alpha-adaptive final vectors reconstruct the actual
canonical middle quotient. The source premise is per-node existence of an
actual MiddleWitness, not bare terminal acceptance. No large common query
support, prior-zero inference, sampler law, or probability is asserted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedMiddleFourAlpha
open Polynomial Finset
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation AspisV5FriConcreteEncoderApplicability
noncomputable section

namespace Generic
variable {K : Type*} [Field K] [DecidableEq K]

/-- Coefficientwise Lagrange interpolation, interleaved in the literal
natural slot order. Neither a received word nor a candidate is an input. -/
def reconstruct {n : Nat} (nodes : Finset K) (final : K → Fin n → K) :
    Fin (4*n) → K := fun i =>
  (Lagrange.interpolate nodes id (fun alpha => final alpha (parentIndex i))).coeff
    (slotIndex i).val

/-- Values of final outside the disclosed node set are irrelevant. -/
theorem reconstruct_local {n : Nat} (nodes : Finset K)
    (left right : K → Fin n → K) (same : ∀ alpha∈nodes, left alpha=right alpha) :
    reconstruct nodes left=reconstruct nodes right := by
  funext i
  unfold reconstruct
  apply congrArg (fun p : K[X] => p.coeff (slotIndex i).val)
  rw [Lagrange.interpolate_apply, Lagrange.interpolate_apply]
  apply Finset.sum_congr rfl
  intro alpha member
  rw [same alpha member]

/-- Four distinct coefficient folds determine every natural coefficient.
Only a cubic polynomial on each four-slot message fibre is interpolated. -/
theorem reconstruct_folds {n : Nat} (nodes : Finset K) (four : nodes.card=4)
    (final : K → Fin n → K) (Q : Fin (4*n) → K)
    (represented : ∀ alpha∈nodes, final alpha=coefficientFoldLayer n alpha Q) :
    reconstruct nodes final=Q := by
  funext i
  let p := monomialPolynomial (fun slot : Fin 4 => Q (childIndex (parentIndex i) slot))
  have degree : p.degree<nodes.card := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    apply WithBot.coe_lt_coe.mpr
    have bounded : p.natDegree≤3 := monomialPolynomial_natDegree_le (by decide) _
    rw [four]
    exact Nat.lt_succ_of_le bounded
  have values (alpha : K) (member : alpha∈nodes) :
      p.eval alpha=final alpha (parentIndex i) := by
    have actual := congrFun (represented alpha member) (parentIndex i)
    rw [coefficientFoldLayer_apply] at actual
    change p.eval alpha=_
    rw [show p=monomialPolynomial
      (fun slot : Fin 4 => Q (childIndex (parentIndex i) slot)) from rfl,
      AspisV8.ShiftedRowPrefix.four_coefficient_eval]
    exact actual.symm
  have interpolated : p=Lagrange.interpolate nodes id
      (fun alpha => final alpha (parentIndex i)) :=
    Lagrange.eq_interpolate_of_eval_eq _ (fun _ _ _ _ h => h) degree values
  calc
    reconstruct nodes final i=p.coeff (slotIndex i).val :=
      congrArg (fun poly : K[X] => poly.coeff (slotIndex i).val) interpolated.symm
    _ = Q (childIndex (parentIndex i) (slotIndex i)) := monomialPolynomial_coeff _ _
    _ = Q i := congrArg Q (childIndex_parentIndex_slotIndex i)

end Generic

open AspisV8.CausalCoveredRecovery AspisV8.SelectedMiddleUniqueness
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact

/-- The chosen later histories may differ at each node. Their actual
finals are forced to be folds of one canonical quotient by source witness
uniqueness, not by supplying a correspondence premise. -/
theorem middle_finals_canonical {q : Nat} (e : Execution q) (gamma : K)
    (nodes : Finset K) (kappa tau : K → K)
    (middle : ∀ alpha∈nodes, ∃ Q,
      MiddleWitness e gamma (kappa alpha) (tau alpha) alpha Q) :
    ∀ alpha∈nodes, (e.strategy gamma (kappa alpha)).final (tau alpha) alpha=
      coefficientFoldLayer 256 alpha (canonical e gamma) := by
  intro alpha member
  obtain ⟨Q, witness⟩ := middle alpha member
  exact canonical_final e gamma (kappa alpha) (tau alpha) alpha Q witness

/-- No candidate input: the reconstruction function reads precisely the
four disclosed final coefficient vectors and their distinct alpha nodes.
Per-node MiddleWitness remains an explicit source event restriction. -/
theorem reconstruct_middle_canonical {q : Nat} (e : Execution q) (gamma : K)
    (nodes : Finset K) (four : nodes.card=4) (kappa tau : K → K)
    (middle : ∀ alpha∈nodes, ∃ Q,
      MiddleWitness e gamma (kappa alpha) (tau alpha) alpha Q) :
    Generic.reconstruct nodes
      (fun alpha => (e.strategy gamma (kappa alpha)).final (tau alpha) alpha)=
      canonical e gamma :=
  Generic.reconstruct_folds (n := 256) nodes four _ (canonical e gamma)
    (middle_finals_canonical e gamma nodes kappa tau middle)

/-- Every other actual middle continuation has the corresponding fold of
the same reconstructed quotient; its alpha is not required to be a node. -/
theorem reconstructed_final {q : Nat} (e : Execution q) (gamma : K)
    (nodes : Finset K) (four : nodes.card=4) (kappa tau : K → K)
    (middle : ∀ alpha∈nodes, ∃ Q,
      MiddleWitness e gamma (kappa alpha) (tau alpha) alpha Q)
    (kappa' tau' alpha' : K) (Q : Fin 1024 → K)
    (witness : MiddleWitness e gamma kappa' tau' alpha' Q) :
    (e.strategy gamma kappa').final tau' alpha'=
      coefficientFoldLayer 256 alpha' (Generic.reconstruct nodes
        (fun alpha => (e.strategy gamma (kappa alpha)).final (tau alpha) alpha)) := by
  rw [reconstruct_middle_canonical e gamma nodes four kappa tau middle]
  exact canonical_final e gamma kappa' tau' alpha' Q witness

#print axioms Generic.reconstruct_local
#print axioms Generic.reconstruct_folds
#print axioms middle_finals_canonical
#print axioms reconstruct_middle_canonical
#print axioms reconstructed_final
end
end AspisV8.SelectedMiddleFourAlpha
