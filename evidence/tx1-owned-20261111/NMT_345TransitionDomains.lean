import NMT_345PaymentDomains
import NMT_345CanonicalLive
import NMT_345CanonicalAfter
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result AspisR1
abbrev CanonicalTransition := AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1

def TransitionDomains (t : CanonicalTransition) : Prop :=
 (∀ d ∈ t.live_snapshot.frontier.val,NJX_DigestCohort.dc d) ∧
 NJX_DigestCohort.dc t.candidate_afterstate.next_root ∧
 (∀ d ∈ t.candidate_afterstate.next_frontier.val,NJX_DigestCohort.dc d)

theorem transition_domains (s : CanonicalStatement)
 (good : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s = .ok (.Ok ())) :
 TransitionDomains (NFY_NBN_StatementResult.common s).lane_transition := by
 obtain ⟨_,live,after⟩ := NFY_NBN_StatementDomains.late_children s good
 have hl := live_canonical _ live
 have ha := after_canonical _ after
 exact ⟨frontier_members _ hl.2,canonical_fin_members _ ha.1,frontier_members _ ha.2⟩
#print axioms transition_domains
end NMT_345
