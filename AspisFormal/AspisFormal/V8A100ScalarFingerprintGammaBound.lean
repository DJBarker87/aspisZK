import AspisFormal.V8A100FixedTupleFingerprint

/-!
# Scalar DEEP checks do not imply component-wise prefix equality

The no-new-tree V8 verifier checks, at each OOD point, only the gamma-batched
scalar obtained from the 29 public component values.  A parser theorem can
show that every restoration branch reuses the same public vectors, but one
such scalar equality does not show that the branch's extracted component
tuple has that complete vector.

This file records the exact replacement needed by the soundness argument.
For a fixed public vector, every nonmatching component vector can satisfy its
gamma dot at at most 28 nonzero gammas.  Outside the existing two-point tuple
collision event, once one family member has the full two-point fingerprint,
all alternative family members are nonmatching at at least one point.  The
actual fixed V7/V8 tuple family has at most 100 members, so the union over all
alternatives has cardinality at most `99 * 28 = 2772`.

It also gives a constructive two-gamma countermodel: a single fixed public
29-vector can match one scalar at one gamma and an independently chosen scalar
at a second gamma.  Thus component-wise equality must not be inferred from
the Rust verifier's gamma-dot checks.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

namespace AspisV8A100ScalarFingerprintGammaBound

open AspisV6Width29CorrelatedAgreement
open AspisV8A100FixedTupleFingerprint
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7Width29ComponentExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV8A100TwoPointDeep

section GenericField

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Nonzero gammas at which one candidate component vector has the same
gamma dot as one fixed public vector. -/
noncomputable def scalarFingerprintMatchSet
    (candidate expected : Fin 29 → K) : Finset K :=
  (Finset.univ.erase 0).filter fun gamma =>
    width29Batch candidate gamma = width29Batch expected gamma

theorem scalarFingerprintMatchSet_card_le_28
    (candidate expected : Fin 29 → K) (different : candidate ≠ expected) :
    (scalarFingerprintMatchSet candidate expected).card ≤ 28 := by
  classical
  let discrepancy : Fin 29 → K := fun lane =>
    candidate lane - expected lane
  have discrepancyNonzero : discrepancy ≠ 0 := by
    intro zero
    apply different
    funext lane
    have atLane := congrFun zero lane
    exact sub_eq_zero.mp atLane
  have sameSet : scalarFingerprintMatchSet candidate expected =
      width29NonzeroCollisionSet discrepancy := by
    ext gamma
    simp only [scalarFingerprintMatchSet, width29NonzeroCollisionSet,
      Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨nonzero, equal⟩
      refine ⟨nonzero, ?_⟩
      rw [show discrepancy = fun lane => candidate lane - expected lane by rfl,
        width29Batch_sub, sub_eq_zero]
      exact equal
    · rintro ⟨nonzero, equal⟩
      refine ⟨nonzero, ?_⟩
      rw [show discrepancy = fun lane => candidate lane - expected lane by rfl,
        width29Batch_sub, sub_eq_zero] at equal
      exact equal
  rw [sameSet]
  exact width29_nonzero_collision_card_le discrepancy discrepancyNonzero

/-- Gammas satisfying both scalar OOD checks for one candidate tuple. -/
noncomputable def twoScalarFingerprintMatchSet
    (candidate0 candidate1 public0 public1 : Fin 29 → K) : Finset K :=
  scalarFingerprintMatchSet candidate0 public0 ∩
    scalarFingerprintMatchSet candidate1 public1

theorem twoScalarFingerprintMatchSet_card_le_28_of_mismatch
    (candidate0 candidate1 public0 public1 : Fin 29 → K)
    (mismatch : candidate0 ≠ public0 ∨ candidate1 ≠ public1) :
    (twoScalarFingerprintMatchSet candidate0 candidate1 public0 public1).card ≤
      28 := by
  rcases mismatch with firstMismatch | secondMismatch
  · exact (Finset.card_le_card (Finset.inter_subset_left)).trans
      (scalarFingerprintMatchSet_card_le_28 candidate0 public0 firstMismatch)
  · exact (Finset.card_le_card (Finset.inter_subset_right)).trans
      (scalarFingerprintMatchSet_card_le_28 candidate1 public1 secondMismatch)

/-! ## Constructive obstruction to component-wise inference -/

/-- A public vector supported in its first two lanes whose gamma dot can be
prescribed independently at two distinct gamma values. -/
noncomputable def twoGammaInterpolatingVector
    (alpha beta atAlpha atBeta : K) : Fin 29 → K :=
  fun lane =>
    if lane.val = 0 then
      atAlpha - alpha * ((atAlpha - atBeta) / (alpha - beta))
    else if lane.val = 1 then
      (atAlpha - atBeta) / (alpha - beta)
    else 0

private theorem width29Batch_twoGammaInterpolatingVector
    (alpha beta atAlpha atBeta gamma : K) :
    width29Batch (twoGammaInterpolatingVector alpha beta atAlpha atBeta)
        gamma =
      (atAlpha - alpha * ((atAlpha - atBeta) / (alpha - beta))) +
        ((atAlpha - atBeta) / (alpha - beta)) * gamma := by
  classical
  simp [width29Batch, twoGammaInterpolatingVector, Fin.sum_univ_succ]

theorem twoGammaInterpolatingVector_at_alpha
    (alpha beta atAlpha atBeta : K) (distinct : alpha ≠ beta) :
    width29Batch (twoGammaInterpolatingVector alpha beta atAlpha atBeta)
        alpha = atAlpha := by
  rw [width29Batch_twoGammaInterpolatingVector]
  field_simp [sub_ne_zero.mpr distinct]
  ring

theorem twoGammaInterpolatingVector_at_beta
    (alpha beta atAlpha atBeta : K) (distinct : alpha ≠ beta) :
    width29Batch (twoGammaInterpolatingVector alpha beta atAlpha atBeta)
        beta = atBeta := by
  rw [width29Batch_twoGammaInterpolatingVector]
  field_simp [sub_ne_zero.mpr distinct]
  ring

/-- Exact countermodel to the inference "same proof-carried vector plus a
successful gamma dot implies the extracted component vector is fixed". -/
theorem exists_fixed_public_vector_matching_two_branch_scalars
    (alpha beta leftScalar rightScalar : K) (distinct : alpha ≠ beta) :
    ∃ vector : Fin 29 → K,
      width29Batch vector alpha = leftScalar ∧
        width29Batch vector beta = rightScalar := by
  exact ⟨twoGammaInterpolatingVector alpha beta leftScalar rightScalar,
    twoGammaInterpolatingVector_at_alpha alpha beta leftScalar rightScalar
      distinct,
    twoGammaInterpolatingVector_at_beta alpha beta leftScalar rightScalar
      distinct⟩

section CandidateFamily

variable {Candidate : Type*} [DecidableEq Candidate]

/-- Gammas at which a nonmatching member of an arbitrary fixed candidate
family passes both public scalar checks.  Keeping this lemma generic avoids
normalizing the large concrete `InitialMessage` representation. -/
noncomputable def nonmatchingScalarGammaSet
    (family : Finset Candidate)
    (vector0 vector1 : Candidate → Fin 29 → K)
    (expected0 expected1 : Fin 29 → K) : Finset K :=
  (family.filter fun candidate =>
      vector0 candidate ≠ expected0 ∨ vector1 candidate ≠ expected1).biUnion
    fun candidate => twoScalarFingerprintMatchSet
      (vector0 candidate) (vector1 candidate) expected0 expected1

theorem nonmatchingScalarGammaSet_card_le
    (family : Finset Candidate)
    (vector0 vector1 : Candidate → Fin 29 → K)
    (expected0 expected1 : Fin 29 → K) :
    (nonmatchingScalarGammaSet family vector0 vector1
      expected0 expected1).card ≤ family.card * 28 := by
  classical
  let nonmatching := family.filter fun candidate =>
    vector0 candidate ≠ expected0 ∨ vector1 candidate ≠ expected1
  have eachBound : ∀ candidate ∈ nonmatching,
      (twoScalarFingerprintMatchSet (vector0 candidate) (vector1 candidate)
        expected0 expected1).card ≤ 28 := by
    intro candidate member
    exact twoScalarFingerprintMatchSet_card_le_28_of_mismatch
      (vector0 candidate) (vector1 candidate) expected0 expected1
      (Finset.mem_filter.mp member).2
  calc
    (nonmatchingScalarGammaSet family vector0 vector1
        expected0 expected1).card ≤ nonmatching.card * 28 := by
      exact Finset.card_biUnion_le_card_mul nonmatching _ 28 eachBound
    _ ≤ family.card * 28 := Nat.mul_le_mul_right 28
      (Finset.card_le_card (Finset.filter_subset _ _))

/-- Passing both scalar checks outside the explicitly unioned gamma set
forces full equality with the two public vectors. -/
theorem full_fingerprint_of_scalar_match_outside
    (family : Finset Candidate) (candidate : Candidate)
    (candidateMember : candidate ∈ family)
    (vector0 vector1 : Candidate → Fin 29 → K)
    (expected0 expected1 : Fin 29 → K) (gamma : K)
    (scalarMatch : gamma ∈ twoScalarFingerprintMatchSet
      (vector0 candidate) (vector1 candidate) expected0 expected1)
    (outsideBad : gamma ∉ nonmatchingScalarGammaSet family
      vector0 vector1 expected0 expected1) :
    vector0 candidate = expected0 ∧ vector1 candidate = expected1 := by
  classical
  by_cases first : vector0 candidate = expected0
  · by_cases second : vector1 candidate = expected1
    · exact ⟨first, second⟩
    · exfalso
      apply outsideBad
      exact Finset.mem_biUnion.mpr ⟨candidate,
        Finset.mem_filter.mpr ⟨candidateMember, Or.inr second⟩, scalarMatch⟩
  · exfalso
    apply outsideBad
    exact Finset.mem_biUnion.mpr ⟨candidate,
      Finset.mem_filter.mpr ⟨candidateMember, Or.inl first⟩, scalarMatch⟩

/-- Explicit no-exact-match case: every scalar-consistent family member's
gamma belongs to the same conservative union. -/
theorem scalar_match_mem_nonmatching_of_no_exact_match
    (family : Finset Candidate) (candidate : Candidate)
    (candidateMember : candidate ∈ family)
    (vector0 vector1 : Candidate → Fin 29 → K)
    (expected0 expected1 : Fin 29 → K) (gamma : K)
    (noExactMatch : ∀ member ∈ family,
      vector0 member ≠ expected0 ∨ vector1 member ≠ expected1)
    (scalarMatch : gamma ∈ twoScalarFingerprintMatchSet
      (vector0 candidate) (vector1 candidate) expected0 expected1) :
    gamma ∈ nonmatchingScalarGammaSet family vector0 vector1
      expected0 expected1 := by
  classical
  exact Finset.mem_biUnion.mpr ⟨candidate,
    Finset.mem_filter.mpr
      ⟨candidateMember, noExactMatch candidate candidateMember⟩, scalarMatch⟩

end CandidateFamily

end GenericField

/-! ## Actual fixed-family specialization -/

private theorem qm31Exact_two_ne_zero : (2 : QM31Exact) ≠ 0 := by
  intro equalZero
  have mapped :
      algebraMap M31Exact QM31Exact (2 : M31Exact) =
        algebraMap M31Exact QM31Exact (0 : M31Exact) := by
    calc
      algebraMap M31Exact QM31Exact (2 : M31Exact) =
          (2 : QM31Exact) := map_ofNat _ 2
      _ = 0 := equalZero
      _ = algebraMap M31Exact QM31Exact (0 : M31Exact) := (map_zero _).symm
  have baseEqual :=
    FaithfulSMul.algebraMap_injective M31Exact QM31Exact mapped
  exact AspisCircleGroupOrder.two_ne_zero_ZModP baseEqual

local instance qm31ExactNeZeroTwo : NeZero (2 : QM31Exact) :=
  ⟨qm31Exact_two_ne_zero⟩

/-- Nonzero gammas at which some family member passes both scalar OOD checks
without carrying the complete public two-point fingerprint.  This definition
covers both cases: there may be no exact fingerprint match, or there may be
one distinguished exact match and several alternatives. -/
noncomputable def nonmatchingTupleScalarGammaSet
    (family : Finset (Width29InitialMessages QM31Exact))
    (parameter0 parameter1 : QM31Exact)
    (public0 public1 : Fin 29 → QM31Exact) : Finset QM31Exact :=
  nonmatchingScalarGammaSet family
    (fun candidate => componentOodVector candidate parameter0)
    (fun candidate => componentOodVector candidate parameter1) public0 public1

theorem nonmatchingTupleScalarGammaSet_card_le
    (family : Finset (Width29InitialMessages QM31Exact))
    (parameter0 parameter1 : QM31Exact)
    (public0 public1 : Fin 29 → QM31Exact) :
    (nonmatchingTupleScalarGammaSet family parameter0 parameter1
      public0 public1).card ≤ family.card * 28 := by
  exact nonmatchingScalarGammaSet_card_le family
    (fun candidate => componentOodVector candidate parameter0)
    (fun candidate => componentOodVector candidate parameter1) public0 public1

/-- Uniform actual-family bound.  Unlike 2772, this conclusion does not
assume that any family member has the complete public fingerprint. -/
theorem fixedWidth29_nonmatching_scalar_gamma_card_le_2800
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (parameter0 parameter1 : QM31Exact)
    (public0 public1 : Fin 29 → QM31Exact) :
    (nonmatchingTupleScalarGammaSet (fixedWidth29TupleList decoder lanes)
      parameter0 parameter1 public0 public1).card ≤ 2800 := by
  have familyBound := fixedWidth29TupleList_card_le_100 decoder lanes
  have unionBound := nonmatchingTupleScalarGammaSet_card_le
    (fixedWidth29TupleList decoder lanes) parameter0 parameter1 public0 public1
  calc
    _ ≤ (fixedWidth29TupleList decoder lanes).card * 28 := unionBound
    _ ≤ 100 * 28 := Nat.mul_le_mul_right 28 familyBound
    _ = 2800 := by norm_num

/-- All nonzero gammas at which any tuple other than `anchor` passes both
public scalar OOD checks. -/
noncomputable def alternateTupleScalarGammaSet
    (family : Finset (Width29InitialMessages QM31Exact))
    (anchor : Width29InitialMessages QM31Exact)
    (parameter0 parameter1 : QM31Exact)
    (public0 public1 : Fin 29 → QM31Exact) : Finset QM31Exact :=
  (family.erase anchor).biUnion fun candidate =>
    twoScalarFingerprintMatchSet
      (componentOodVector candidate parameter0)
      (componentOodVector candidate parameter1) public0 public1

/-- Outside the two-point collision event, an anchor carrying the complete
public fingerprint leaves at most 28 gammas per alternative tuple. -/
theorem alternateTupleScalarGammaSet_card_le
    (family : Finset (Width29InitialMessages QM31Exact))
    (anchor : Width29InitialMessages QM31Exact)
    (anchorMember : anchor ∈ family)
    (parameter0 parameter1 : QM31Exact)
    (finite0 : AspisV8A100TwoPointDeep.circleDenominator parameter0 ≠ 0)
    (finite1 : AspisV8A100TwoPointDeep.circleDenominator parameter1 ≠ 0)
    (outside : (parameter0, parameter1) ∉
      familyTwoPointCollisions family) :
    (alternateTupleScalarGammaSet family anchor parameter0 parameter1
      (componentOodVector anchor parameter0)
      (componentOodVector anchor parameter1)).card ≤
        (family.card - 1) * 28 := by
  classical
  let alternatives := family.erase anchor
  have eachBound : ∀ candidate ∈ alternatives,
      (twoScalarFingerprintMatchSet
        (componentOodVector candidate parameter0)
        (componentOodVector candidate parameter1)
        (componentOodVector anchor parameter0)
        (componentOodVector anchor parameter1)).card ≤ 28 := by
    intro candidate candidateMember
    have inFamily : candidate ∈ family :=
      (Finset.mem_erase.mp candidateMember).2
    have different : candidate ≠ anchor := by
      exact (Finset.mem_erase.mp candidateMember).1
    have mismatch :
        componentOodVector candidate parameter0 ≠
            componentOodVector anchor parameter0 ∨
          componentOodVector candidate parameter1 ≠
            componentOodVector anchor parameter1 := by
      by_cases first : componentOodVector candidate parameter0 =
          componentOodVector anchor parameter0
      · by_cases second : componentOodVector candidate parameter1 =
            componentOodVector anchor parameter1
        · have equal := eq_of_two_component_vectors_of_not_collision family
            candidate anchor inFamily anchorMember parameter0 parameter1 finite0
            finite1 first second outside
          exact False.elim (different equal)
        · exact Or.inr second
      · exact Or.inl first
    exact twoScalarFingerprintMatchSet_card_le_28_of_mismatch
      (componentOodVector candidate parameter0)
      (componentOodVector candidate parameter1)
      (componentOodVector anchor parameter0)
      (componentOodVector anchor parameter1) mismatch
  calc
    (alternateTupleScalarGammaSet family anchor parameter0 parameter1
        (componentOodVector anchor parameter0)
        (componentOodVector anchor parameter1)).card ≤
        alternatives.card * 28 := by
      exact Finset.card_biUnion_le_card_mul alternatives _ 28 eachBound
    _ = (family.card - 1) * 28 := by
      rw [show alternatives = family.erase anchor by rfl,
        Finset.card_erase_of_mem anchorMember]

/-- The exact deployed fixed-family cap gives 99 alternative tuples and the
release-relevant scalar bad-gamma numerator 2772. -/
theorem fixedWidth29_alternate_scalar_gamma_card_le_2772
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (anchor : Width29InitialMessages QM31Exact)
    (anchorMember : anchor ∈ fixedWidth29TupleList decoder lanes)
    (parameter0 parameter1 : QM31Exact)
    (finite0 : AspisV8A100TwoPointDeep.circleDenominator parameter0 ≠ 0)
    (finite1 : AspisV8A100TwoPointDeep.circleDenominator parameter1 ≠ 0)
    (outside : (parameter0, parameter1) ∉
      familyTwoPointCollisions (fixedWidth29TupleList decoder lanes)) :
    (alternateTupleScalarGammaSet (fixedWidth29TupleList decoder lanes)
      anchor parameter0 parameter1
      (componentOodVector anchor parameter0)
      (componentOodVector anchor parameter1)).card ≤ 2772 := by
  have familyBound := fixedWidth29TupleList_card_le_100 decoder lanes
  have unionBound := alternateTupleScalarGammaSet_card_le
    (fixedWidth29TupleList decoder lanes) anchor anchorMember parameter0
    parameter1 finite0 finite1 outside
  calc
    _ ≤ ((fixedWidth29TupleList decoder lanes).card - 1) * 28 := unionBound
    _ ≤ 99 * 28 := by omega
    _ = 2772 := by norm_num

#print axioms scalarFingerprintMatchSet_card_le_28
#print axioms twoScalarFingerprintMatchSet_card_le_28_of_mismatch
#print axioms twoGammaInterpolatingVector_at_alpha
#print axioms twoGammaInterpolatingVector_at_beta
#print axioms exists_fixed_public_vector_matching_two_branch_scalars
#print axioms nonmatchingScalarGammaSet_card_le
#print axioms full_fingerprint_of_scalar_match_outside
#print axioms scalar_match_mem_nonmatching_of_no_exact_match
#print axioms nonmatchingTupleScalarGammaSet_card_le
#print axioms fixedWidth29_nonmatching_scalar_gamma_card_le_2800
#print axioms alternateTupleScalarGammaSet_card_le
#print axioms fixedWidth29_alternate_scalar_gamma_card_le_2772

end AspisV8A100ScalarFingerprintGammaBound
