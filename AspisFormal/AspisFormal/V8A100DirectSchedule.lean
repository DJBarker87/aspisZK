import AspisFormal.V5BoundedQuerySamplerUniformity
import AspisFormal.V6BinaryFrontier

/-!
# V8-A100 direct q22 schedule and binary-frontier arithmetic

This file instantiates the already-proved ideal bounded-sampler law at the
V8 parameters and proves the exact numeric frontier/body bounds used by the
research Rust profile.  The frontier theorem is stated at the existing
`V6BinaryFrontier` source-model boundary: the adjacent-XOR model must satisfy
the ordinary occupied-block capacity at each of the eighteen levels.
-/

set_option autoImplicit false

namespace AspisV8A100DirectSchedule

open AspisV5BoundedQuerySamplerUniformity
open AspisV6BinaryFrontier

abbrev Position := Fin (2 ^ 18)
abbrev Schedule := Fin 22 ↪ Position

/-- The V8 schedule type itself carries the exact count, range, and
no-duplicate properties. -/
theorem schedule_position_lt_domain (schedule : Schedule) (i : Fin 22) :
    (schedule i).val < 2 ^ 18 :=
  (schedule i).isLt

theorem schedule_positions_distinct (schedule : Schedule) :
    Function.Injective schedule :=
  schedule.injective

/-- Conditioned on success, the exact ideal law of the bounded q22 sampler is
uniform over ordered injections. -/
theorem q22_conditioned_schedule_uniform (schedule : Schedule) :
    conditionedScheduleProbability (maxDraws := 64) schedule =
      (1 : ℝ) / Fintype.card Schedule := by
  exact conditionedScheduleProbability_eq_uniform schedule (by norm_num) (by norm_num)

/-- The unconditioned experiment counts draw-budget exhaustion as rejection;
therefore it needs no success-conditioning correction in the soundness bound. -/
theorem q22_exhaustion_is_rejection (bad : Finset Position) :
    unconditionedSuccessfulBadProbability (q := 22) (maxDraws := 64) bad ≤
      AspisV5WithoutReplacementQuerySoundness.idealMissProbability
        (q := 22) bad := by
  exact unconditionedSuccessfulBadProbability_le_ideal bad (by norm_num) (by norm_num)

/-- Telescoping identity for the exact signed source frontier model. -/
private theorem level_balance_telescopes (depth : Nat)
    (occupied : Nat → Nat) :
    (∑ level ∈ Finset.range depth,
      ((2 * occupied (level + 1) : Int) - occupied level)) =
      (occupied depth : Int) - occupied 0 +
        ∑ level ∈ Finset.range depth, (occupied (level + 1) : Int) := by
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, inductionHypothesis]
      ring

/-- At level `level + 1`, twenty-two leaves can occupy at most twenty-two
blocks and at most all `2^(17-level)` blocks present at that height.  These
eighteen simultaneous capacity bounds force the exact source frontier to be
at most 296. -/
theorem q22_source_frontier_le_296
    (height : Fin 21 → Nat)
    (heightBound : ∀ gap, height gap < 18)
    (occupiedCapacity : ∀ level ∈ Finset.range 18,
      occupiedFromAdjacent height (level + 1) ≤
        min 22 (2 ^ (17 - level))) :
    levelWalkSigned 18 height ≤ 296 := by
  have occupiedTop : occupiedFromAdjacent height 18 = 1 := by
    simp [occupiedFromAdjacent, Nat.not_le.mpr (heightBound _)]
  have occupiedBottom : occupiedFromAdjacent height 0 = 22 := by
    simp [occupiedFromAdjacent]
  have capacitySum :
      (∑ level ∈ Finset.range 18, min 22 (2 ^ (17 - level))) = 317 := by
    norm_num [Finset.sum_range_succ]
  have occupiedSum :
      (∑ level ∈ Finset.range 18,
        occupiedFromAdjacent height (level + 1)) ≤ 317 := by
    calc
      (∑ level ∈ Finset.range 18,
          occupiedFromAdjacent height (level + 1)) ≤
          ∑ level ∈ Finset.range 18, min 22 (2 ^ (17 - level)) := by
            exact Finset.sum_le_sum fun level membership ↦
              occupiedCapacity level membership
      _ = 317 := capacitySum
  rw [levelWalkSigned, level_balance_telescopes, occupiedTop, occupiedBottom]
  have occupiedSumInt :
      (∑ level ∈ Finset.range 18,
        (occupiedFromAdjacent height (level + 1) : Int)) ≤ 317 := by
    exact_mod_cast occupiedSum
  omega

/-- Adjacent highest-differing-bit values of the explicit maximum fixture. -/
def maximumFixtureHeight : Fin 21 → Nat := ![
  14, 15, 14, 16, 14, 15, 14, 17, 14, 15, 13,
  14, 13, 16, 13, 14, 13, 15, 13, 14, 13
]

/-- The Rust fixture positions, represented without a proof-carrying sorted
wrapper so that their XOR heights can be checked directly. -/
def maximumFixtureQueries : Fin 22 → Nat := ![
  0, 16384, 32768, 49152, 65536, 81920, 98304, 114688,
  131072, 147456, 163840, 172032, 180224, 188416, 196608,
  204800, 212992, 221184, 229376, 237568, 245760, 253952
]

theorem maximumFixture_xor_height (gap : Fin 21) :
    adjacentXorHeight maximumFixtureQueries gap = maximumFixtureHeight gap := by
  fin_cases gap <;>
    rfl

theorem maximumFixture_height_bound (gap : Fin 21) :
    adjacentXorHeight maximumFixtureQueries gap < 18 := by
  rw [maximumFixture_xor_height]
  fin_cases gap <;> norm_num [maximumFixtureHeight]

/-- The explicit q22 fixture attains the upper bound in the exact optimized
adjacent-XOR expression used by Rust. -/
theorem maximumFixture_attains_296 :
    adjacentPrefixExpanded 18
        (adjacentXorHeight maximumFixtureQueries) - 22 = 296 := by
  have heights : adjacentXorHeight maximumFixtureQueries = maximumFixtureHeight := by
    funext gap
    exact maximumFixture_xor_height gap
  rw [heights]
  norm_num [adjacentPrefixExpanded, maximumFixtureHeight, Fin.sum_univ_succ]

theorem maximumFixture_levelWalk_eq_296 :
    levelWalkSigned 18 (adjacentXorHeight maximumFixtureQueries) = 296 := by
  rw [levelWalkSigned_eq_checkedSub
    (adjacentXorHeight maximumFixtureQueries)
    maximumFixture_height_bound (by
      rw [show adjacentXorHeight maximumFixtureQueries = maximumFixtureHeight by
        funext gap
        exact maximumFixture_xor_height gap]
      norm_num [adjacentPrefixExpanded, maximumFixtureHeight,
        Fin.sum_univ_succ])]
  exact_mod_cast maximumFixture_attains_296

/-- Exact V8 wire-body and pair-Pool verifier-account maxima. -/
theorem q22_two_vector_body_bytes :
    10804 + 2 * 26 + 24 + 22 * 621 + 2 * 296 * 26 = 39934 := by
  norm_num

theorem q22_complete_pair_verifier_account_bytes :
    40 + 688 + 39934 = 40662 := by
  norm_num

#print axioms schedule_position_lt_domain
#print axioms schedule_positions_distinct
#print axioms q22_conditioned_schedule_uniform
#print axioms q22_exhaustion_is_rejection
#print axioms q22_source_frontier_le_296
#print axioms maximumFixture_xor_height
#print axioms maximumFixture_attains_296
#print axioms maximumFixture_levelWalk_eq_296
#print axioms q22_two_vector_body_bytes
#print axioms q22_complete_pair_verifier_account_bytes

end AspisV8A100DirectSchedule
