import ComponentRows
import QuotientOriginalCore

/-!
Source-review draft: same-tuple component claims after the new middle-image
recovery. One nonzero ordinary component-error polynomial is chosen before
gamma. Its roots cover any represented, ordinary-row-correct quotient whose
87 claims are not all exact. There is no union over three rows or87 cells.

The family, tuple coefficients, three point functionals and claimed values
precede gamma. The Data/Rows record and inactive scalar may depend on gamma;
they are NOT inputs to the exceptional set. Zero of the complete ordinary
error vector is explicit, not inferred from one sampled-kappa equality.
For an already fixed family of cardinality at most one, the same uniform
exception costs at most28 gammas, even if its member and Q are chosen later.
No semantic residual, acceptance, sampler or payment theorem is claimed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedMiddleComponentClaims
open Polynomial Finset
open AspisV8.ClaimTransport AspisV8.ShiftedRowPrefix AspisV8.OODInterpolant
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

abbrev Tuple (K : Type*) := Fin 29 → Fin 1024 → K
abbrev Weights (K : Type*) := Fin 4 → Fin 1024 → K
abbrev Claims (K : Type*) := Fin 3 → Fin 29 → K

def ExactClaims (p : Tuple K) (weights : Weights K) (claimed : Claims K) : Prop :=
  ∀ row lane, claimed row lane = covector (weights row.succ) (p lane)

def rowError (p : Tuple K) (weights : Weights K) (claimed : Claims K)
    (row : Fin 3) : K[X] :=
  errorPolynomial (covector (weights row.succ)) p (claimed row)

/-- The choice uses fixed coefficients only. The zero case has no root
charge and is proved below to mean that every component claim is exact. -/
def chosenError (p : Tuple K) (weights : Weights K) (claimed : Claims K) : K[X] :=
  if bad : ∃ row, rowError p weights claimed row ≠ 0 then
    rowError p weights claimed bad.choose
  else 0

theorem chosenError_degree (p : Tuple K) (weights : Weights K) (claimed : Claims K) :
    (chosenError p weights claimed).natDegree ≤ 28 := by
  classical
  unfold chosenError
  split_ifs
  · exact component_error_degree _ _ _
  · simp

theorem claims_exact_of_chosen_zero (p : Tuple K) (weights : Weights K)
    (claimed : Claims K) (zero : chosenError p weights claimed = 0) :
    ExactClaims p weights claimed := by
  classical
  have allZero : ∀ row, rowError p weights claimed row = 0 := by
    intro row
    by_contra wrong
    have bad : ∃ row, rowError p weights claimed row ≠ 0 := ⟨row, wrong⟩
    rw [chosenError, dif_pos bad] at zero
    exact bad.choose_spec zero
  intro row lane
  have coefficient := component_error_coeff (covector (weights row.succ)) p (claimed row) lane
  change (rowError p weights claimed row).coeff lane.val =
    claimed row lane - covector (weights row.succ) (p lane) at coefficient
  rw [allZero row, Polynomial.coeff_zero] at coefficient
  exact sub_eq_zero.mp coefficient.symm

def badGammas (Gamma : Finset K) (p : Tuple K) (weights : Weights K)
    (claimed : Claims K) : Finset K :=
  if chosenError p weights claimed = 0 then ∅
  else Gamma.filter fun gamma => (chosenError p weights claimed).eval gamma = 0

theorem badGammas_subset (Gamma : Finset K) (p : Tuple K) (weights : Weights K)
    (claimed : Claims K) : badGammas Gamma p weights claimed ⊆ Gamma := by
  classical
  unfold badGammas
  split_ifs
  · exact Finset.empty_subset _
  · exact Finset.filter_subset _ _

theorem badGammas_card (Gamma : Finset K) (p : Tuple K) (weights : Weights K)
    (claimed : Claims K) : (badGammas Gamma p weights claimed).card ≤ 28 := by
  classical
  unfold badGammas
  split_ifs with zero
  · simp
  · have roots : (Gamma.filter fun gamma =>
        (chosenError p weights claimed).eval gamma = 0).val ⊆
          (chosenError p weights claimed).roots := by
      intro gamma present
      exact (Polynomial.mem_roots zero).mpr (Finset.mem_filter.mp present).2
    exact (Polynomial.card_le_degree_of_subset_roots roots).trans
      (chosenError_degree p weights claimed)

variable [NeZero (2 : K)]

/-- This is the actual corrected ordinary-row construction. Representation
uses the SAME Q and tuple; the inactive scalar is arbitrary. -/
theorem represented_rows_force_root (d : Data (K := K)) (quarter : K)
    (weights : Weights K) (claimed : Claims K) (inactive : K)
    (Q : Fin 1024 → K) (p : Tuple K)
    (represented : d.original Q = batch d.gamma p)
    (rowZero : (ComponentRows.rows d quarter weights claimed inactive Q).errors = 0) :
    (chosenError p weights claimed).eval d.gamma = 0 := by
  classical
  unfold chosenError
  split_ifs with bad
  · have same : ComponentRows.original d Q = batch d.gamma p := represented
    have source := ComponentRows.recovered_point_error d quarter weights claimed inactive Q p
      same bad.choose
    rw [rowZero] at source
    exact source.symm
  · simp

/-- A zero ordinary-row vector and a represented quotient imply all87
claims, except at the one fixed error polynomial's roots. No image/own-support
premise is needed AGAIN once the actual representation has been proved. -/
theorem claims_or_root (Gamma : Finset K) (p : Tuple K) (weights : Weights K)
    (claimed : Claims K) (d : Data (K := K)) (quarter inactive : K)
    (Q : Fin 1024 → K) (inside : d.gamma ∈ Gamma)
    (represented : d.original Q = batch d.gamma p)
    (rowZero : (ComponentRows.rows d quarter weights claimed inactive Q).errors = 0) :
    ExactClaims p weights claimed ∨ d.gamma ∈ badGammas Gamma p weights claimed := by
  classical
  by_cases zero : chosenError p weights claimed = 0
  · exact Or.inl (claims_exact_of_chosen_zero p weights claimed zero)
  · right
    rw [badGammas, if_neg zero]
    exact Finset.mem_filter.mpr ⟨inside,
      represented_rows_force_root d quarter weights claimed inactive Q p represented rowZero⟩

/-- The family is fixed before gamma; membership may be witnessed later.
An empty or singleton family contributes no multiplicative loss beyond28. -/
def familyBad (Gamma : Finset K) (family : Finset (Tuple K)) (weights : Weights K)
    (claimed : Claims K) : Finset K :=
  family.biUnion fun p => badGammas Gamma p weights claimed

theorem familyBad_subset (Gamma : Finset K) (family : Finset (Tuple K))
    (weights : Weights K) (claimed : Claims K) : familyBad Gamma family weights claimed ⊆ Gamma := by
  classical
  intro gamma present
  obtain ⟨p, _, hit⟩ := Finset.mem_biUnion.mp present
  exact badGammas_subset Gamma p weights claimed hit

theorem familyBad_card (Gamma : Finset K) (family : Finset (Tuple K))
    (one : family.card ≤ 1) (weights : Weights K) (claimed : Claims K) :
    (familyBad Gamma family weights claimed).card ≤ 28 := by
  classical
  have unionBound : (familyBad Gamma family weights claimed).card ≤ family.card * 28 :=
    Finset.card_biUnion_le_card_mul family (fun p => badGammas Gamma p weights claimed) 28
      (fun p _ => badGammas_card Gamma p weights claimed)
  have product := Nat.mul_le_mul_right 28 one
  omega

/-- Direct consumer for the family constructed by
SelectedMiddleImageRecovery.exists_recovery. All gamma-dependent Data,
inactive, quotient and member choices remain quantified AFTER the fixed set.
This is a deterministic root exclusion, not a uniform/Fiat--Shamir law. -/
theorem family_claims_exact (Gamma : Finset K) (family : Finset (Tuple K))
    (weights : Weights K) (claimed : Claims K)
    (d : Data (K := K)) (quarter inactive : K) (Q : Fin 1024 → K)
    (p : Tuple K) (member : p ∈ family) (inside : d.gamma ∈ Gamma)
    (outside : d.gamma ∉ familyBad Gamma family weights claimed)
    (represented : d.original Q = batch d.gamma p)
    (rowZero : (ComponentRows.rows d quarter weights claimed inactive Q).errors = 0) :
    ExactClaims p weights claimed := by
  classical
  rcases claims_or_root Gamma p weights claimed d quarter inactive Q inside represented rowZero
    with exactClaims | hit
  · exact exactClaims
  · exact False.elim (outside (Finset.mem_biUnion.mpr ⟨p, member, hit⟩))

#print axioms chosenError_degree
#print axioms claims_exact_of_chosen_zero
#print axioms badGammas_subset
#print axioms badGammas_card
#print axioms represented_rows_force_root
#print axioms claims_or_root
#print axioms familyBad_subset
#print axioms familyBad_card
#print axioms family_claims_exact
end
end AspisV8.SelectedMiddleComponentClaims
