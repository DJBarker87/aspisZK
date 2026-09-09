import MaskedCurveRepresentation
import AspisFormal.V5FriJohnsonListBound

/-! A static full-slot quotient family. One differing coefficient lane gives
the overlap bound: there is no four-lane union and no global polynomiality
premise on the received word. The family bound is mathematical, not a decoder. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.QuotientFamilyCore
open Finset
open AspisV8.MaskedCurveRepresentation
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriJohnsonListBound
noncomputable section
variable {K F : Type*} [Field K] [DecidableEq K] [Field F] [Algebra F K]

theorem different_lane {n : Nat} (Q Q' : Fin (4*n) → K) (different : Q≠Q') :
    ∃ lane : Fin 4, coefficientLane n lane Q≠coefficientLane n lane Q' := by
  classical
  by_contra none
  have lanes : (fun lane => coefficientLane n lane Q)=
      (fun lane => coefficientLane n lane Q') := by
    funext lane
    by_contra unequal
    exact none ⟨lane,unequal⟩
  exact different ((interleave_lanes n Q).symm.trans
    ((congrArg (interleave n) lanes).trans (interleave_lanes n Q')))

theorem fullSupport_eq_joint {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K)) (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (received : Fin (4*m) → K) (Q : Fin (4*n) → K) :
    fullSupport encoder x y received Q=
      jointAgreementSet encoder (decodedLanes inverse2x inverse2y received)
        (fun lane => coefficientLane n lane Q) := by
  rw [joint_eq_full encoder x y inverse2x inverse2y hx hy,interleave_lanes]

theorem fullSupport_intersection_le {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K)) (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (overlap : ∀ p p' : Fin n → K, p≠p' →
      (agreementSet (encoder p) (encoder p')).card≤255)
    (received : Fin (4*m) → K) (Q Q' : Fin (4*n) → K) (different : Q≠Q') :
    ((fullSupport encoder x y received Q)∩
      (fullSupport encoder x y received Q')).card≤255 := by
  classical
  obtain ⟨lane,unequal⟩ := different_lane Q Q' different
  rw [fullSupport_eq_joint encoder x y inverse2x inverse2y hx hy,
    fullSupport_eq_joint encoder x y inverse2x inverse2y hx hy]
  apply le_trans (Finset.card_le_card (show
    jointAgreementSet encoder (decodedLanes inverse2x inverse2y received)
      (fun lane => coefficientLane n lane Q) ∩
    jointAgreementSet encoder (decodedLanes inverse2x inverse2y received)
      (fun lane => coefficientLane n lane Q') ⊆
    agreementSet (encoder (coefficientLane n lane Q))
      (encoder (coefficientLane n lane Q')) from ?_))
    (overlap _ _ unequal)
  intro i member
  have left := (Finset.mem_filter.mp (Finset.mem_inter.mp member).1).2 lane
  have right := (Finset.mem_filter.mp (Finset.mem_inter.mp member).2).2 lane
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,left.symm.trans right⟩

/-- Apply the existing Johnson theorem to an arbitrary finite subfamily;
all arithmetic is a small real/natural certificate, not field enumeration. -/
theorem finite_subfamily_card_le_99 {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K)) (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (domain : m=262144)
    (overlap : ∀ p p' : Fin n → K, p≠p' →
      (agreementSet (encoder p) (encoder p')).card≤255)
    (received : Fin (4*m) → K) (candidates : Finset (Fin (4*n) → K))
    (large : ∀ Q∈candidates, 9558≤(fullSupport encoder x y received Q).card) :
    candidates.card≤99 := by
  classical
  let Candidate := {Q // Q∈candidates}
  let agreement : Candidate → Finset (Fin m) := fun c => fullSupport encoder x y received c.1
  have floor : ∀ c : Candidate, 9558≤(agreement c).card := fun c => large c.1 c.2
  have pairwise : ∀ c d : Candidate, c≠d → ((agreement c)∩(agreement d)).card≤255 := by
    intro c d different
    exact fullSupport_intersection_le encoder x y inverse2x inverse2y hx hy overlap
      received c.1 d.1 (fun same => different (Subtype.ext same))
  have forbidden : Fintype.card Candidate<100 :=
    list_card_lt_of_johnson_parameters agreement 262144 9558 255 100
      ((Fintype.card_fin m).trans domain) floor pairwise
      (by norm_num) (by norm_num) (by norm_num)
  rw [Fintype.card_coe] at forbidden
  omega

/-- A bounded literal predicate family, with membership equivalence, rather
than a coverage-only list that could silently contain additional candidates. -/
theorem exact_finite_family {A : Type*} [Fintype A] (predicate : A → Prop)
    (limit : Nat) (bound : ∀ candidates : Finset A,
      (∀ c∈candidates, predicate c) → candidates.card≤limit) :
    ∃ family : Finset A, family.card≤limit ∧ ∀ c, c∈family ↔ predicate c := by
  classical
  let family := Finset.univ.filter predicate
  refine ⟨family,bound family (fun c member => (Finset.mem_filter.mp member).2),?_⟩
  intro c
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ c))

#print axioms fullSupport_eq_joint
#print axioms fullSupport_intersection_le
#print axioms finite_subfamily_card_le_99
#print axioms exact_finite_family
end
end AspisV8.QuotientFamilyCore
