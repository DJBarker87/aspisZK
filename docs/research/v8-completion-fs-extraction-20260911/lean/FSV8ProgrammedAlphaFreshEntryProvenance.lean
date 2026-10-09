import FSV8ProgrammedAlphaPrefixInsertionProvenance
import AspisFormal.K1.V7Tag73VerifierOracleStability

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000

namespace AspisV8Completion.FSV8ProgrammedAlphaFreshEntryProvenance

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73VerifierOracleStability

theorem run_machine_lookup_of_initially_absent_is_fresh
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (state : OracleState) (program : OracleMachine Result)
    (input : ShaInput) (entry : TableEntry)
    (initialMissing : lookupEntry state input = none)
    (finalFound : lookupEntry
      (runMachine controller limits actor fuel state program).oracle input =
        some entry) :
    ∃ record ∈ historySince state
        (runMachine controller limits actor fuel state program).oracle,
      record.actor = actor ∧ record.origin = .fresh ∧
        record.input = input ∧ record.output = entry.output ∧
        entry = freshTableEntryOfRecord record := by
  have entryMember : entry ∈
      (runMachine controller limits actor fuel state program).oracle.table := by
    unfold lookupEntry at finalFound
    exact List.mem_of_find?_eq_some finalFound
  have extension :
      (runMachine controller limits actor fuel state program).oracle.table =
        state.table ++ verifierFreshTableEntries state
          (runMachine controller limits actor fuel state program).oracle :=
    (run_machine_exact_fresh_extension controller limits actor fuel state
      program).1
  have entryInput : entry.input = input := by
    unfold lookupEntry at finalFound
    exact of_decide_eq_true (List.find?_eq_some_iff_append.mp finalFound).1
  have notInitial : entry ∉ state.table := by
    intro stateMember
    unfold lookupEntry at initialMissing
    have rejected := List.find?_eq_none.mp initialMissing entry stateMember
    simp [entryInput] at rejected
  have newMember : entry ∈ verifierFreshTableEntries state
      (runMachine controller limits actor fuel state program).oracle := by
    rw [extension] at entryMember
    exact (List.mem_append.mp entryMember).resolve_left notInitial
  have suffixMember : entry ∈
      ((runMachine controller limits actor fuel state program).oracle.table).drop
        state.table.length := by
    rw [extension]
    simpa using newMember
  simpa [entryInput] using
    (run_machine_new_entry_is_fresh_and_initially_absent
      controller limits actor fuel state program entry suffixMember).2.2

#print axioms run_machine_lookup_of_initially_absent_is_fresh

end AspisV8Completion.FSV8ProgrammedAlphaFreshEntryProvenance
