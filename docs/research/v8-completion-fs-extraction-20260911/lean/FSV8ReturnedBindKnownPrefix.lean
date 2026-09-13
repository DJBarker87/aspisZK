import FSV8ReturnedBindMachineSplit
import AspisFormal.K1.V7Tag73VerifierOracleStability

/-!
# Final oracle of a bind with a known returned prefix

The source-shaped V8 cuts identify the value returned by each prefix, but
some older cut interfaces deliberately discarded the whole-bind final-oracle
equality.  This leaf recovers that equality from the operational bind split
and the known prefix result.  It is purely deterministic: no acceptance,
freshness, target, or probability premise is introduced.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8ReturnedBindKnownPrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73SharedOracleVerifierRunner
open FSV8ReturnedBindMachineSplit

/-- Once the first machine's returned value is fixed, a successful bind has
the same final oracle as the literal continuation from that value and the
actual residual fuel. -/
theorem runMachine_bind_final_oracle_eq_of_known_prefix
    {First Second : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine First)
    (next : First → OracleMachine Second) (value : First) (result : Second)
    (prefixReturned :
      (runMachine controller limits actor fuel state program).halt =
        .returned value)
    (success :
      (runMachine controller limits actor fuel state
        (bindOracleMachine program next)).halt = .returned result) :
    let prefixRun := runMachine controller limits actor fuel state program
    (runMachine controller limits actor fuel state
        (bindOracleMachine program next)).oracle =
      (runMachine controller limits actor (fuel - prefixRun.steps)
        prefixRun.oracle (next value)).oracle := by
  obtain ⟨actual, actualPrefixReturned, _continuationReturned,
      finalOracle, _steps⟩ :=
    runMachine_bind_returned_split controller limits actor fuel state program
      next result success
  have valueExact : actual = value := by
    exact MachineHalt.returned.inj (actualPrefixReturned.symm.trans prefixReturned)
  subst actual
  exact finalOracle

/-- Every ordinary machine run extends, rather than rewrites, its entry
history.  This source invariant is used to carry a fresh marker record through
the later verifier continuations. -/
theorem runMachine_entry_history_prefix_final
    {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (fuel : Nat) (state : OracleState)
    (program : OracleMachine Result) :
    state.history <+:
      (runMachine controller limits actor fuel state program).oracle.history := by
  obtain ⟨appended, historyExact, _tableExact, _properties, _length⟩ :=
    AspisK1.V7Tag73VerifierOracleStability.run_machine_fresh_extension_data
      controller limits actor fuel state program
  exact ⟨appended, historyExact.symm⟩

#print axioms runMachine_bind_final_oracle_eq_of_known_prefix
#print axioms runMachine_entry_history_prefix_final

end AspisV8Completion.FSV8ReturnedBindKnownPrefix
