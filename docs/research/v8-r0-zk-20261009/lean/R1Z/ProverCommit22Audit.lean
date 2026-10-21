import R1Z.ProverCommitFuel22
import R1Z.ProverCommitFuelMass22
import R1Z.ProverCommitFuelJoin22
import R1Z.ProverCommitDeployedFuel22
import R1Z.ProverCommitTreeMap22
import R1Z.ProverCommitSemanticSampler22
import R1Z.ProverCommitCircleSampler22
import R1Z.ProverCommitFuelOracle22
/-! Final focused closure and axioms audit. This is not a frozen release
manifest replay and does not assert either concrete WholeRunJoin. -/
set_option autoImplicit false
namespace R1Z.ProverCommit22Audit

theorem protocol_constants : ProverCommitFuel22.fuel = ProverCommitFuelMass22.k ∧
    ProverCommitFuel22.instances = ProverCommitFuelMass22.count := ⟨rfl,rfl⟩

/-- Three calls of at most five draws stay in the first fifteen counters.
No assumption about a generic callback's termination is inferred. -/
theorem counter_room (calls draws : Nat) (hc : calls ≤ 3) (hd : draws ≤ 5) :
    calls * draws ≤ 15 ∧ calls * draws < 2^64 := by
  have h := Nat.mul_le_mul hc hd
  constructor
  · exact h
  · exact lt_of_le_of_lt h (by norm_num)

#print axioms protocol_constants
#print axioms counter_room
#print axioms R1Z.ProverCommitFuel22.agrees
#print axioms R1Z.ProverCommitFuel22.stable
#print axioms R1Z.ProverCommitFuelMass22.exhaustion_mass
#print axioms R1Z.ProverCommitFuelMass22.charge_le
#print axioms R1Z.ProverCommitFuelMass22.union_bound
#print axioms R1Z.ProverCommitFuelMass22.old_contained
#print axioms R1Z.ProverCommitFuelMass22.augmented_mass
#print axioms R1Z.ProverCommitFuelMass22.total_lt_target
#print axioms R1Z.ProverCommitFuelJoin22.failure_mass
#print axioms R1Z.ProverCommitFuelJoin22.old_contained
#print axioms R1Z.ProverCommitFuelJoin22.mass
#print axioms R1Z.ProverCommitFuelJoin22.test_bound
#print axioms R1Z.ProverCommitDeployedFuel22.legacy_refinement_implies
#print axioms R1Z.ProverCommitDeployedFuel22.seed_refinement_implies
#print axioms R1Z.ProverCommitDeployedFuel22.privacy_headline_deployed
#print axioms R1Z.ProverCommitTreeMap22.lookup_of_graph
#print axioms R1Z.ProverCommitTreeMap22.lookup_toList
#print axioms R1Z.ProverCommitTreeMap22.insert_lookup
#print axioms R1Z.ProverCommitTreeMap22.program_collision
#print axioms R1Z.ProverCommitTreeMap22.enumerated
#print axioms R1Z.ProverCommitTreeMap22.writes_transport
#print axioms R1Z.ProverCommitTreeMap22.enumeration_order
#print axioms R1Z.ProverCommitSemanticSampler22.field_pos
#print axioms R1Z.ProverCommitSemanticSampler22.digits_as_tuple
#print axioms R1Z.ProverCommitSemanticSampler22.model_qm31
#print axioms R1Z.ProverCommitSemanticSampler22.sample_qm31
#print axioms R1Z.ProverCommitSemanticSampler22.sample_semChal
#print axioms R1Z.ProverCommitSemanticSampler22.sample_total_semChal
#print axioms R1Z.ProverCommitCircleSampler22.parameter_eq
#print axioms R1Z.ProverCommitCircleSampler22.encoded_coordinates
#print axioms R1Z.ProverCommitCircleSampler22.circle_total_coordinates
#print axioms R1Z.ProverCommitFuelOracle22.window_injective
#print axioms R1Z.ProverCommitFuelOracle22.window_uniform
#print axioms R1Z.ProverCommitFuelOracle22.window_mass
#print axioms R1Z.ProverCommitFuelJoin22.of_seed
#print axioms R1Z.ProverCommitDeployedFuel22.WholeRunJoin.tests
#print axioms R1Z.PrivacyR1HeadlineDeployed.privacy_headline_deployed
#print axioms AspisR1CircleSampleWrapper.RawCircleSampleActualPolicyUnconditionalV1.sampler_total_canonical
#print axioms AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackCoordinatesV1.firstFallbackCoordinates
#print axioms AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackCoordinatesV1.secondFallbackCoordinates
end R1Z.ProverCommit22Audit
