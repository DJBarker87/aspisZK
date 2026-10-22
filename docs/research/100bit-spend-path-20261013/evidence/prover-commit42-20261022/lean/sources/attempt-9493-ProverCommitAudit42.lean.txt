import R1Z.ProverCommitCarrierJoin42
import R1Z.ProverCommitCharged42
import R1Z.ProverCommitContextBounds42
import R1Z.ProverCommitGlobal42
import R1Z.ProverCommitGlobalRun42
import R1Z.ProverCommitNormalCarrier42
import R1Z.ProverCommitOwnerBytes42
import R1Z.ProverCommitOwnerLedger42
import R1Z.ProverCommitOwnerModel42
import R1Z.ProverCommitOwnerRun42
import R1Z.ProverCommitOwnerSuccess42
import R1Z.ProverCommitOwnerZero42
import R1Z.ProverCommitPrivateBounds42
import R1Z.ProverCommitPrivatePairs42
import R1Z.ProverCommitRawFresh42
import R1Z.ProverCommitRetryOwner42
import R1Z.ProverCommitDeployedFuel22

/-! Focused final dependency/axioms audit; not a full release manifest or a
whole-runtime security theorem. -/
#print axioms R1Z.ProverCommitCarrierJoin42.uVec_normalize
#print axioms R1Z.ProverCommitCarrierJoin42.public_nonce_fixed
#print axioms R1Z.ProverCommitCarrierJoin42.private_seeds_retained
#print axioms R1Z.ProverCommitCarrierJoin42.charged_hit_mass
#print axioms R1Z.ProverCommitCharged42.hit_private
#print axioms R1Z.ProverCommitContextBounds42.context_frozen_mass
#print axioms R1Z.ProverCommitContextBounds42.normalized_local
#print axioms R1Z.ProverCommitContextBounds42.global_private_address
#print axioms R1Z.ProverCommitGlobal42.posE_index
#print axioms R1Z.ProverCommitGlobal42.normalized_attVec
#print axioms R1Z.ProverCommitGlobal42.normalized_rest
#print axioms R1Z.ProverCommitGlobal42.causal
#print axioms R1Z.ProverCommitGlobal42.conditional_law
#print axioms R1Z.ProverCommitGlobalRun42.run_eq
#print axioms R1Z.ProverCommitGlobalRun42.continuation
#print axioms R1Z.ProverCommitNormalCarrier42.vec_update
#print axioms R1Z.ProverCommitNormalCarrier42.block_sec
#print axioms R1Z.ProverCommitNormalCarrier42.block_rest
#print axioms R1Z.ProverCommitNormalCarrier42.normalize_lens
#print axioms R1Z.ProverCommitOwnerBytes42.byte_zero
#print axioms R1Z.ProverCommitOwnerBytes42.block_zero
#print axioms R1Z.ProverCommitOwnerBytes42.zero_block
#print axioms R1Z.ProverCommitOwnerBytes42.raw_good
#print axioms R1Z.ProverCommitOwnerLedger42.prepared_model
#print axioms R1Z.ProverCommitOwnerLedger42.continuation
#print axioms R1Z.ProverCommitOwnerModel42.next_eq
#print axioms R1Z.ProverCommitOwnerModel42.run_model
#print axioms R1Z.ProverCommitOwnerModel42.generate_model
#print axioms R1Z.ProverCommitOwnerRun42.fuel_sub
#print axioms R1Z.ProverCommitOwnerRun42.run_exact
#print axioms R1Z.ProverCommitOwnerRun42.generate_exact
#print axioms R1Z.ProverCommitOwnerSuccess42.run_nonce
#print axioms R1Z.ProverCommitOwnerSuccess42.generate_nonce
#print axioms R1Z.ProverCommitOwnerSuccess42.source_success
#print axioms R1Z.ProverCommitOwnerZero42.next_index
#print axioms R1Z.ProverCommitOwnerZero42.zero_from
#print axioms R1Z.ProverCommitOwnerZero42.zero_spec
#print axioms R1Z.ProverCommitPrivateBounds42.src_private
#print axioms R1Z.ProverCommitPrivateBounds42.seed_field
#print axioms R1Z.ProverCommitPrivateBounds42.vector_answer
#print axioms R1Z.ProverCommitPrivateBounds42.answer_field
#print axioms R1Z.ProverCommitPrivateBounds42.private_pair
#print axioms R1Z.ProverCommitPrivateBounds42.fixed_mass
#print axioms R1Z.ProverCommitPrivateBounds42.frozen_mass
#print axioms R1Z.ProverCommitPrivatePairs42.publicSec_update
#print axioms R1Z.ProverCommitPrivatePairs42.vector_update
#print axioms R1Z.ProverCommitPrivatePairs42.answer_parts
#print axioms R1Z.ProverCommitPrivatePairs42.seed_inv
#print axioms R1Z.ProverCommitPrivatePairs42.answer_inv
#print axioms R1Z.ProverCommitPrivatePairs42.pair_all
#print axioms R1Z.ProverCommitPrivatePairs42.pair_mass
#print axioms R1Z.ProverCommitRawFresh42.ne_binding
#print axioms R1Z.ProverCommitRawFresh42.raw_off_bindings
#print axioms R1Z.ProverCommitRawFresh42.raw_off_prefix
#print axioms R1Z.ProverCommitRetryOwner42.entropy_model
#print axioms R1Z.ProverCommitRetryOwner42.eight_model
#print axioms R1Z.ProverCommitDeployedFuel22.privacy_headline_deployed
