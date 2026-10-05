import AspisV8Privacy.SeparatorObstruction
import AspisV8Privacy.RetryFailureBound
import AspisV8PairedCommitment.ForwardHop
import AspisV8R19.AdaptiveFirstReadLaw
import AspisV8R19.R414Q22CacheHitDistance
import AspisV8R19.R417Q22SuccessLaw
import AspisV8R19.R605GuardedFieldLaw
import AspisV8R19.R931AdaptiveSuccessDomination
import AspisV8R19.R945CircleObservationLaw

/-!
V8 audit 2026-10-05, Phase 1: oracle, probability and generic-composition
privacy nodes discharged by a theorem already in the tree at 4e0f47381.
Statements only; every proof term is the name of an existing theorem.
-/
set_option autoImplicit false
namespace V8Audit.Privacy

/-- P40. Hybrid triangle: event-distance bounds `ε₁` and `ε₂` on two consecutive
finite games give `ε₁ + ε₂` on the composite. -/
def Node_P40 : Prop := type_of% @AspisV8Privacy.event_distance_trans.{0, 0, 0, 0}
theorem node_P40 : Node_P40 := @AspisV8Privacy.event_distance_trans.{0, 0, 0, 0}

/-- P41. A bijection of prover coins that commutes with the observation gives
identical observation laws (the coupling step of a mask-translation argument). -/
def Node_P41 : Prop := type_of% @AspisV8Privacy.sameUniformLaw_of_coinEquiv.{0, 0, 0}
theorem node_P41 : Node_P41 := @AspisV8Privacy.sameUniformLaw_of_coinEquiv.{0, 0, 0}

/-- P42. If each attempt fails with conditional probability at most `1 - a`,
the probability of `n` consecutive failures is at most `(1 - a)^n`. -/
def Node_P42 : Prop := type_of% @AspisV8Privacy.bounded_retry_failure
theorem node_P42 : Node_P42 := @AspisV8Privacy.bounded_retry_failure

/-- P43 (negative control). A same-public witness pair with a test of advantage
above `2ε` excludes every statement-only `ε`-simulator. -/
def Node_P43 : Prop :=
  type_of% @AspisV8Privacy.no_statement_only_simulator_of_pairwise_separator.{0, 0, 0, 0, 0, 0}
theorem node_P43 : Node_P43 :=
  @AspisV8Privacy.no_statement_only_simulator_of_pairwise_separator.{0, 0, 0, 0, 0, 0}

/-- P44. Finite causal paired-commitment hop: along any forward trace of
commitment-oracle steps, the eager and delayed views differ on any test by at
most the weight of the bad-coin event. -/
def Node_P44 : Prop :=
  type_of% @AspisV8PairedCommitment.finite_witness_retaining_commitment_hop.{0, 0, 0, 0}
theorem node_P44 : Node_P44 :=
  @AspisV8PairedCommitment.finite_witness_retaining_commitment_hop.{0, 0, 0, 0}

/-- P45. Adaptive first-read law: a memoised oracle program whose every reached
address is unread has exactly the law of the same program run on fresh
independent uniform answers, for adaptive addresses and stopping. -/
def Node_P45 : Prop := type_of% @AspisV8R19.AdaptiveFirstReadLaw.lazyMean_eq_independentMean
theorem node_P45 : Node_P45 := @AspisV8R19.AdaptiveFirstReadLaw.lazyMean_eq_independentMean

/-- P46. q22 challenge under a cache: for any prior table, the memoised q22
challenge program is within the cache-hit mass of the ideal candidate kernel. -/
def Node_P46 : Prop := type_of% @AspisV8R19.R414Q22CacheHitDistance.challenge_distance
theorem node_P46 : Node_P46 := @AspisV8R19.R414Q22CacheHitDistance.challenge_distance

/-- P47. QM31 field challenge under a cache: the probability of any fixed
field value is within the non-fresh mass of its exact ideal value. -/
def Node_P47 : Prop := type_of% @AspisV8R19.R605GuardedFieldLaw.cached_field_mass_distance
theorem node_P47 : Node_P47 := @AspisV8R19.R605GuardedFieldLaw.cached_field_mass_distance

/-- P48. Conditioned on success, the bounded q22 scan is uniform over legal
query schedules. -/
def Node_P48 : Prop := type_of% @AspisV8R19.R417Q22SuccessLaw.uniform_success
theorem node_P48 : Node_P48 := @AspisV8R19.R417Q22SuccessLaw.uniform_success

/-- P49. Exact output law of the three-attempt circle sampler on independent
answers, with parameter exhaustion and challenge exhaustion kept as separate
outcomes of stated mass. -/
def Node_P49 : Prop := type_of% @AspisV8R19.R945CircleObservationLaw.circleProgram_observation_law
theorem node_P49 : Node_P49 := @AspisV8R19.R945CircleObservationLaw.circleProgram_observation_law

/-- P50. Per-stage successful-output density bounds valid from every starting
state compose through any finite adaptive sequence of sampler stages. -/
def Node_P50 : Prop :=
  type_of% @AspisV8R19.R931AdaptiveSuccessDomination.adaptive_success_domination
theorem node_P50 : Node_P50 :=
  @AspisV8R19.R931AdaptiveSuccessDomination.adaptive_success_domination

#print axioms node_P40
#print axioms node_P41
#print axioms node_P42
#print axioms node_P43
#print axioms node_P44
#print axioms node_P45
#print axioms node_P46
#print axioms node_P47
#print axioms node_P48
#print axioms node_P49
#print axioms node_P50
end V8Audit.Privacy
