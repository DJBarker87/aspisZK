import AspisFormal.V8A100TwoPointDeep
import AspisFormal.Pool.V7FixedWidth29TupleList

/-!
# Two secure-circle fingerprints select one fixed width-29 tuple

The existing V7 correlated theorem permits the close combined message to vary
with gamma.  The stronger causal object already present in the repository is
`fixedWidth29TupleList`, a family of at most 100 jointly close component
tuples fixed by the C1/C2 received words before gamma.

This file proves the deterministic and counting part of the proposed V8
repair.  A differing component message can collide at at most 1024 finite
rational-circle parameters.  Therefore two component-wise vectors collide
for one ordered tuple pair at at most `1024^2` parameter pairs, and the whole
fixed family has at most `100^2 * 1024^2 = 10,485,760,000` bad ordered
parameter pairs.  This deliberately uses ordered pairs; it is a conservative
factor-two relaxation of the unordered-pair count, not a heuristic.

The theorem is independent of the random-oracle scheduling law.  A later
source theorem must show that the two accepted parameters are sampled from
the claimed conditional law and that all restored continuations consume the
same fixed tuple family.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisV8A100FixedTupleFingerprint

open Polynomial
open AspisV5FriCircleEncoderDistance
open AspisV5FriInitialCircleEncoderIdentity
open AspisV8A100TwoPointDeep
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7Width29ComponentExtraction
open AspisPool.V7FixedWidth29TupleList
open AspisV5ComponentCQM31TowerExact

section GenericExtension

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [NeZero (2 : K)]

abbrev InitialMessageK := Fin 1024 → K
abbrev Width29TupleK := Fin 29 → InitialMessageK (K := K)

/-- All finite rational-chart parameters at which two actual initial circle
messages have the same value. -/
noncomputable def messageCollisionParameters
    (left right : InitialMessageK (K := K)) : Finset K :=
  Finset.univ.filter fun parameter =>
    circleDenominator parameter ≠ 0 ∧
      initialCircleValue left parameter = initialCircleValue right parameter

theorem messageCollisionParameters_card_le_1024
    (numeratorInjective : Function.Injective
      (fun message : InitialMessageK (K := K) =>
        circleNumerator (initialP0 message) (initialP1 message)))
    (left right : InitialMessageK (K := K)) (different : left ≠ right) :
    (messageCollisionParameters left right).card ≤ 1024 := by
  classical
  let difference : K[X] :=
    circleNumerator (initialP0 left) (initialP1 left) -
      circleNumerator (initialP0 right) (initialP1 right)
  have differenceNonzero : difference ≠ 0 := by
    intro zero
    apply different
    exact numeratorInjective (sub_eq_zero.mp zero)
  have degreeBound : difference.natDegree ≤ 1024 := by
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (circleNumerator_natDegree_le _ _)
        (circleNumerator_natDegree_le _ _))
  have subset :
      (messageCollisionParameters left right).val ⊆ difference.roots := by
    intro parameter member
    have conditions := (Finset.mem_filter.mp member).2
    rw [Polynomial.mem_roots differenceNonzero]
    change difference.eval parameter = 0
    unfold difference
    rw [Polynomial.eval_sub,
      circleNumerator_eval_initialCircleValue left parameter conditions.1,
      circleNumerator_eval_initialCircleValue right parameter conditions.1,
      conditions.2, sub_self]
  exact (Polynomial.card_le_degree_of_subset_roots subset).trans degreeBound

noncomputable def componentOodVector
    (components : Width29TupleK (K := K)) (parameter : K) : Fin 29 → K :=
  fun lane => initialCircleValue (components lane) parameter

noncomputable def tupleCollisionParameters
    (left right : Width29TupleK (K := K)) : Finset K :=
  Finset.univ.filter fun parameter =>
    circleDenominator parameter ≠ 0 ∧
      componentOodVector left parameter = componentOodVector right parameter

theorem tupleCollisionParameters_card_le_1024
    (numeratorInjective : Function.Injective
      (fun message : InitialMessageK (K := K) =>
        circleNumerator (initialP0 message) (initialP1 message)))
    (left right : Width29TupleK (K := K)) (different : left ≠ right) :
    (tupleCollisionParameters left right).card ≤ 1024 := by
  classical
  have laneDifferent : ∃ lane, left lane ≠ right lane := by
    simpa only [Function.ne_iff] using different
  obtain ⟨lane, differentAtLane⟩ := laneDifferent
  have subset : tupleCollisionParameters left right ⊆
      messageCollisionParameters (left lane) (right lane) := by
    intro parameter member
    have conditions := (Finset.mem_filter.mp member).2
    change parameter ∈ Finset.univ.filter (fun parameter =>
      circleDenominator parameter ≠ 0 ∧
        initialCircleValue (left lane) parameter =
          initialCircleValue (right lane) parameter)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, conditions.1, ?_⟩
    exact congrFun conditions.2 lane
  exact (Finset.card_le_card subset).trans
    (messageCollisionParameters_card_le_1024
      numeratorInjective (left lane) (right lane) differentAtLane)

/-- Both component vectors collide for the same ordered tuple pair. -/
noncomputable def tupleTwoPointCollisions
    (left right : Width29TupleK (K := K)) : Finset (K × K) :=
  tupleCollisionParameters left right ×ˢ tupleCollisionParameters left right

theorem tupleTwoPointCollisions_card_le
    (numeratorInjective : Function.Injective
      (fun message : InitialMessageK (K := K) =>
        circleNumerator (initialP0 message) (initialP1 message)))
    (left right : Width29TupleK (K := K)) (different : left ≠ right) :
    (tupleTwoPointCollisions left right).card ≤ 1024 * 1024 := by
  classical
  simp only [tupleTwoPointCollisions, Finset.card_product]
  exact Nat.mul_le_mul
    (tupleCollisionParameters_card_le_1024
      numeratorInjective left right different)
    (tupleCollisionParameters_card_le_1024
      numeratorInjective left right different)

noncomputable def orderedDistinctTuplePairs
    (family : Finset (Width29TupleK (K := K))) :
    Finset (Width29TupleK (K := K) × Width29TupleK (K := K)) :=
  (family.product family).filter fun pair => pair.1 ≠ pair.2

theorem orderedDistinctTuplePairs_card_le_square
    (family : Finset (Width29TupleK (K := K))) :
    (orderedDistinctTuplePairs family).card ≤ family.card * family.card := by
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The complete deterministic two-vector collision event for a fixed family.
Membership means that some two distinct family members have identical full
29-component vectors at both parameters. -/
noncomputable def familyTwoPointCollisions
    (family : Finset (Width29TupleK (K := K))) : Finset (K × K) :=
  (orderedDistinctTuplePairs family).biUnion fun pair =>
    tupleTwoPointCollisions pair.1 pair.2

theorem familyTwoPointCollisions_card_le
    (numeratorInjective : Function.Injective
      (fun message : InitialMessageK (K := K) =>
        circleNumerator (initialP0 message) (initialP1 message)))
    (family : Finset (Width29TupleK (K := K))) :
    (familyTwoPointCollisions family).card ≤
      family.card * family.card * (1024 * 1024) := by
  classical
  calc
    (familyTwoPointCollisions family).card ≤
        (orderedDistinctTuplePairs family).card * (1024 * 1024) := by
      apply Finset.card_biUnion_le_card_mul
      intro pair member
      have different := (Finset.mem_filter.mp member).2
      exact tupleTwoPointCollisions_card_le
        numeratorInjective pair.1 pair.2 different
    _ ≤ family.card * family.card * (1024 * 1024) :=
      Nat.mul_le_mul_right _ (orderedDistinctTuplePairs_card_le_square family)

/-- Outside the explicit collision event, two disclosed component vectors
select at most one member of the fixed family. -/
theorem eq_of_two_component_vectors_of_not_collision
    (family : Finset (Width29TupleK (K := K)))
    (left right : Width29TupleK (K := K))
    (leftMember : left ∈ family) (rightMember : right ∈ family)
    (t0 t1 : K)
    (finite0 : circleDenominator t0 ≠ 0)
    (finite1 : circleDenominator t1 ≠ 0)
    (firstEqual : componentOodVector left t0 = componentOodVector right t0)
    (secondEqual : componentOodVector left t1 = componentOodVector right t1)
    (outside : (t0, t1) ∉ familyTwoPointCollisions family) :
    left = right := by
  classical
  by_contra different
  apply outside
  rw [familyTwoPointCollisions]
  apply Finset.mem_biUnion.mpr
  refine ⟨(left, right), ?_, ?_⟩
  · rw [orderedDistinctTuplePairs, Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨leftMember, rightMember⟩, different⟩
  · change (t0, t1) ∈
      (tupleCollisionParameters left right).product
        (tupleCollisionParameters left right)
    apply Finset.mem_product.mpr
    constructor
    · change t0 ∈ Finset.univ.filter (fun parameter =>
        circleDenominator parameter ≠ 0 ∧
          componentOodVector left parameter = componentOodVector right parameter)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, finite0, firstEqual⟩
    · change t1 ∈ Finset.univ.filter (fun parameter =>
        circleDenominator parameter ≠ 0 ∧
          componentOodVector left parameter = componentOodVector right parameter)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, finite1, secondEqual⟩

end GenericExtension

/-! ## Exact V7/V8 fixed-family specialization -/

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

/-- Exact conservative ordered-pair numerator for the real fixed family. -/
theorem fixedWidth29TwoPointCollisions_card_le_10485760000
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact) :
    (familyTwoPointCollisions (fixedWidth29TupleList decoder lanes)).card ≤
      10485760000 := by
  have familyBound := fixedWidth29TupleList_card_le_100 decoder lanes
  have numeratorInjective : Function.Injective
      (fun message : InitialMessage QM31Exact =>
        circleNumerator (initialP0 message) (initialP1 message)) :=
    exactInitialEncoderCircleRealization.numerator_injective
  calc
    (familyTwoPointCollisions (fixedWidth29TupleList decoder lanes)).card ≤
        (fixedWidth29TupleList decoder lanes).card *
          (fixedWidth29TupleList decoder lanes).card * (1024 * 1024) :=
      familyTwoPointCollisions_card_le numeratorInjective _
    _ ≤ 100 * 100 * (1024 * 1024) := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul familyBound familyBound)
    _ = 10485760000 := by norm_num

theorem fixedWidth29_eq_of_two_component_vectors
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (left right : Width29InitialMessages QM31Exact)
    (leftMember : left ∈ fixedWidth29TupleList decoder lanes)
    (rightMember : right ∈ fixedWidth29TupleList decoder lanes)
    (t0 t1 : QM31Exact)
    (finite0 : circleDenominator t0 ≠ 0)
    (finite1 : circleDenominator t1 ≠ 0)
    (firstEqual : componentOodVector left t0 = componentOodVector right t0)
    (secondEqual : componentOodVector left t1 = componentOodVector right t1)
    (outside : (t0, t1) ∉
      familyTwoPointCollisions (fixedWidth29TupleList decoder lanes)) :
    left = right :=
  eq_of_two_component_vectors_of_not_collision
    (fixedWidth29TupleList decoder lanes) left right
    leftMember rightMember t0 t1 finite0 finite1
    firstEqual secondEqual outside

#print axioms messageCollisionParameters_card_le_1024
#print axioms tupleCollisionParameters_card_le_1024
#print axioms tupleTwoPointCollisions_card_le
#print axioms familyTwoPointCollisions_card_le
#print axioms eq_of_two_component_vectors_of_not_collision
#print axioms fixedWidth29TwoPointCollisions_card_le_10485760000
#print axioms fixedWidth29_eq_of_two_component_vectors

end AspisV8A100FixedTupleFingerprint
