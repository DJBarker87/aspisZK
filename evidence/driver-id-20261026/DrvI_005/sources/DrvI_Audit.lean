import DrvI_SourceCounterexample
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvI_Audit
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortRuntimeBindingC7

/-- Explicit consistent model, not a claimed native accepted fixture. Both
verifiers are Physical, one accepts, and the arbitrary driver rejects. -/
theorem nonvacuity (adapter : AdapterRw.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (i : OraclePortStoredExperimentC4.Input) (H : Bytes → State) :
    Port1_StoredCarrier.Physical (fun _ => .done true) ∧
    Port1_StoredCarrier.Physical
      (Port1_Driver.rust adapter DrvI_Counterexample.silent D hash) ∧
    (eval H (.done true : Program Bytes State Bool)).2 = true ∧
    (.done true : Program Bytes State Bool) ≠
      Port1_Driver.rust adapter DrvI_Counterexample.silent D hash i := by
  exact ⟨fun _ _ _ _ => rfl,
    DrvI_SourceCounterexample.physical_counterinstance adapter D hash, rfl,
    DrvI_SourceCounterexample.accepting_source_differs adapter D hash (fun _ => .done true) i H rfl⟩

#print axioms nonvacuity
#print axioms AspisR1.DrvI_Counterexample.call_results
#print axioms AspisR1.DrvI_Counterexample.call_trace
#print axioms AspisR1.DrvI_Counterexample.silent_stages
#print axioms AspisR1.DrvI_Counterexample.queried_stages
#print axioms AspisR1.DrvI_Counterexample.stages_differ
#print axioms AspisR1.DrvI_Counterexample.no_universal_identification
#print axioms AspisR1.DrvI_Installation.same_batch_dictionary
#print axioms AspisR1.DrvI_Installation.installed_split
#print axioms AspisR1.DrvI_Installation.silent_not_installed
#print axioms AspisR1.DrvI_Installation.installed_call_success
#print axioms AspisR1.DrvI_SourceCounterexample.silent_driver
#print axioms AspisR1.DrvI_SourceCounterexample.accepting_source_differs
#print axioms AspisR1.DrvI_SourceCounterexample.physical_counterinstance
#print nonvacuity
#print AspisR1.DrvI_Counterexample.no_universal_identification
#print AspisR1.DrvI_SourceCounterexample.accepting_source_differs
end AspisR1.DrvI_Audit
end
