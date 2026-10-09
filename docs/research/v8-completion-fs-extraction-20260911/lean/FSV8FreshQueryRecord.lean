import AspisFormal.K1.V7Tag73VerifierOracleStability
import AspisFormal.K1.V7Tag73OperationalCausalInjection

/-!
# Exact record created by a successful missing oracle query

The alpha-marker target argument needs the literal pre-query state, not merely
an input/output pair found later in a flattened trace.  This leaf records the
deterministic state transition of a successful query whose input was absent.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8FreshQueryRecord

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalCausalInjection

/-- A successful query at an absent input is exactly one fresh transition.
In particular, its history record retains the actual pre-query state, actor,
input, and answer. -/
theorem successful_missing_query_is_fresh_successor
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (missing : lookupEntry state input = none)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    nextState = freshQueryState actor state input output := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    split at success
    next entry found =>
      rw [missing] at found
      contradiction
    next missingAtRun =>
      split at success <;> try contradiction
      next _ =>
        split at success
        next _ => contradiction
        next answer answered =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          rfl

/-- History-level spelling of the same transition. -/
theorem successful_missing_query_appends_fresh_record
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (missing : lookupEntry state input = none)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    nextState.history = state.history ++
      [{ input := input, output := output, actor := actor, origin := .fresh }] := by
  rw [successful_missing_query_is_fresh_successor controller limits actor state
    nextState input output missing success]
  rfl

#print axioms successful_missing_query_is_fresh_successor
#print axioms successful_missing_query_appends_fresh_record

end AspisV8Completion.FSV8FreshQueryRecord
