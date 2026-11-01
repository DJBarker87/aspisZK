import PV_B3P_P227_08
import PV_B3P_LinkDefinitions13227
import PV_B3P_TransitionAdapter543227
namespace PV_B3P_Association543227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false
/-- Exact fresh ae1-2 target, with hash-checked same-origin callees reused.
Only the declaration name changes. No recurrence or constant is evaluated. -/
def fresh_transition_reference543
  (public1 : reference_terminal.SemanticPublic) :
  Result (core.result.Result Unit
    reference_terminal.PoolV1PairForestSemanticTerminalErrorV1)
  := do
  let b ←
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      public1.transition.live_snapshot.pool public1.pool
  if b
  then
    ok (core.result.Result.Err
      reference_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
  else
    let b1 ←
      core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
        public1.transition.live_snapshot.deployment_domain
        public1.deployment_domain
    if b1
    then
      ok (core.result.Result.Err
        reference_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
    else
      if public1.transition.live_snapshot.sequence !=
        public1.transition.live_snapshot.next_pair_index
      then
        ok (core.result.Result.Err
          reference_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
      else
        let i ←
          aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
        if public1.transition.live_snapshot.next_pair_index >= i
        then
          ok (core.result.Result.Err
            reference_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
        else
          let b2 ←
            reference_terminal.checked_next227
              public1.transition.live_snapshot.next_pair_index
              public1.transition.candidate_afterstate.next_pair_index
          if b2
          then
            ok (core.result.Result.Err
              reference_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
          else
            let carry ←
              reference_terminal.bounded_append_carry
                public1.transition.live_snapshot.next_pair_index
            let pending_return ←
              reference_terminal.validate_transition_loop
                public1.transition.live_snapshot.next_pair_index
                public1.transition.live_snapshot.frontier
                public1.transition.candidate_afterstate.next_frontier carry
                0#usize
            match pending_return with
            | none => ok (core.result.Result.Ok ())
            | some r => ok r

theorem transition_reference_equality543 :
    fresh_transition_reference543 = reference_terminal.validate_transition := by
  funext input
  rfl

theorem transition_reference_link543 :
    PV_B3P_Links13227.PV_B3P_Link_terminal_validate_transition fresh_transition_reference543 :=
  transition_reference_equality543

#print axioms transition_reference_equality543
#print axioms transition_reference_link543
end PV_B3P_Association543227
