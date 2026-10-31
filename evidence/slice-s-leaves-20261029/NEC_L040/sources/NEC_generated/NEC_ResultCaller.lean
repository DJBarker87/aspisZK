import JHb_S2K_ResultBinding
set_option autoImplicit false
namespace NEC_ResultCaller
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal
abbrev Statement := PoolV1PairForestTerminalStatementV1
abbrev Output := PoolV1PairForestTerminalResultV1
abbrev Error := PoolV1PairForestTerminalFormatErrorV1
abbrev derived := AspisR1.S2K.ResultAdmission.value

def PacketDomain (s : Statement) (r : Output) : Prop := r=derived s

theorem caller_domain (s : Statement) : PacketDomain s (derived s) := rfl

/-- All six actual result fields are constructed by emit_result before the
binding validator call; this packet does not cover unrelated external callers. -/
theorem fields (s : Statement) :
 (derived s).transition_kind=(match s with | .PrivateTransfer _ _=>.PrivateTransfer | .Withdrawal _ _=>.Withdrawal) ∧
 (derived s).master_account=(AspisR1.S2K.StatementAdmission.common s).master_account ∧
 (derived s).selected_lane_account=(AspisR1.S2K.StatementAdmission.common s).selected_lane_account ∧
 (derived s).output_lane=(AspisR1.S2K.StatementAdmission.common s).output_lane ∧
 (derived s).nullifier=AspisR1.S2K.StatementAdmission.nullifier s ∧
 (derived s).verified_afterstate=(AspisR1.S2K.StatementAdmission.common s).lane_transition.candidate_afterstate := by
 cases s <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem accepted (s : Statement) (r : Output) (domain : PacketDomain s r)
 (child : validate_pool_v1_pair_forest_terminal_statement_v1 s=ok (.Ok ())) :
 validate_pool_v1_pair_forest_terminal_result_against_statement_v1 s r=ok (.Ok ()) := by
 rw [domain]
 exact AspisR1.S2K.ResultBinding.validated s child

theorem rejected (s : Statement) (r : Output) (error : Error)
 (child : validate_pool_v1_pair_forest_terminal_statement_v1 s=ok (.Err error)) :
 validate_pool_v1_pair_forest_terminal_result_against_statement_v1 s r=ok (.Err error) := by
 unfold validate_pool_v1_pair_forest_terminal_result_against_statement_v1
 rw [child]
 rfl

#print axioms caller_domain
#print axioms fields
#print axioms accepted
#print axioms rejected
end NEC_ResultCaller
