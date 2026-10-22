import R1Z.ProverCommitTrustedStd24
import R1Z.ProverCommitCounter24
import R1Z.ProverCommitMapProgram24
import R1Z.ProverCommitFreshWindow24
import R1Z.ProverCommitFuelFactor24
import R1Z.PrivacyR1HeadlineDeployed
import R1Z.ProverCommitDeployedFuel22
/-! One final changed-cone axioms audit. No concrete shipped-source instance
or source-policy equivalence is supplied by this audit. -/
#print axioms R1Z.ProverCommitTrustedStd24.writes
#print axioms R1Z.ProverCommitTrustedStd24.lookup
#print axioms R1Z.ProverCommitTrustedStd24.iteration
#print axioms R1Z.ProverCommitTrustedStd24.tls_run_native
#print axioms R1Z.ProverCommitTrustedStd24.tls_schedule
#print axioms R1Z.ProverCommitTrustedStd24.model_consistent
#print axioms R1Z.ProverCommitCounter24.next_counter
#print axioms R1Z.ProverCommitCounter24.advance_no_wrap
#print axioms R1Z.ProverCommitCounter24.positive
#print axioms R1Z.ProverCommitCounter24.accounting
#print axioms R1Z.ProverCommitCounter24.three_search_room
#print axioms R1Z.ProverCommitCounter24.three_agrees
#print axioms R1Z.ProverCommitMapProgram24.run_decode
#print axioms R1Z.ProverCommitMapProgram24.empty_run
#print axioms R1Z.ProverCommitFreshWindow24.linear_fresh
#print axioms R1Z.ProverCommitFreshWindow24.cursor_injective
#print axioms R1Z.ProverCommitFreshWindow24.observer_fresh
#print axioms R1Z.ProverCommitFreshWindow24.earlier_coin_fresh
#print axioms R1Z.ProverCommitFreshWindow24.source_window_fresh
#print axioms R1Z.ProverCommitFuelFactor24.no_deterministic_factor
#print axioms R1Z.ProverCommitFuelFactor24.tape_nontrivial
#print axioms R1Z.ProverCommitFuelFactor24.runJoin_not_model_function
#print axioms R1Z.PrivacyR1HeadlineDeployed.privacy_headline_deployed
#print axioms R1Z.ProverCommitDeployedFuel22.privacy_headline_deployed

/- The retained raw sampler wrapper passes a state transformer where its
external ABI requires an iterator state. The repaired expression is typed,
but typing does not establish source equivalence or helper refinement. -/
section SamplerABI
open Aeneas Aeneas.Std
variable (iter : core.slice.iter.IterMut U32)
variable (into_iter_back : core.slice.iter.IterMut U32 → Array U32 8#usize)
variable (back : core.slice.iter.IterMut U32 → core.slice.iter.IterMut U32)
#check_failure into_iter_back back
#check into_iter_back (back iter)
end SamplerABI
