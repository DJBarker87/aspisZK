import SCC_Physical
import CPH_Nonvacuity
import Rc5_Top
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCC_Nonvacuity
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPH_FixtureData
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_TwoPass

/-- The adopted game/persistence fixture and both successful local wrappers
coexist with a mismatching accepted runtime view. This is an interface witness,
NOT a cryptographic source fixture or an inhabitant of all Rc5 hypotheses.
In particular n1/n2 are CPH's local witnesses, not source-extraction facts. -/
theorem game_with_unassociated (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (P : Prover) (H : Bytes → State) :
    CPH_Game.DeployedPairExecution observations false true e1 e2 saved suffix
      n1 n2 copy allocator id ∧
    CPR_DataPersistence.TwoTransactionLaw
      (adjacent observations) (ordinary observations (Hist_Nonvacuity.key 0#u8))
      (before observations) (tentative observations) (success observations) (loaded observations) ∧
    first n1 copy allocator e1 id data1 () = ok (.Ok (saved,CPH_FixtureWrappers.post1,())) ∧
    second n2 allocator e2 id data2 slot () = ok (.Ok (e2.heap,())) ∧
    observations.physicalEvents false ≠ [] ∧
    ∃ (runtime : F3T_Runtime.Runtime) (run : RunView),
      eval H runtime = ([],some run) ∧ run.2.2 = true ∧
      run.2.1.stored ≠ (eval H P).2.stored ∧
      ¬ SCC_Physical.StoredInputLaw P runtime ∧
      (∀ rust : Verifier, ¬ SCC_Physical.FirstPassBinding rust P runtime) := by
  obtain ⟨_,_,_,_,game,persistence,accepted1,accepted2,_,events,_⟩ :=
    CPH_Nonvacuity.joint_runtime data1 data2 slot
  exact ⟨game,persistence,accepted1,accepted2,events,
    SCC_Physical.accepted_unassociated P H⟩

#print axioms game_with_unassociated
#print axioms AspisR1.SCC_Physical.stored_of_first
#print axioms AspisR1.SCC_Physical.changed_stored
#print axioms AspisR1.SCC_Physical.accepted_unassociated
#print axioms AspisR1.SCC_Physical.preserve_conditions
#print axioms AspisR1.CPH_Nonvacuity.joint_runtime
#print axioms AspisR1.Rc5_Top.deployed
#print AspisR1.SCC_Physical.FirstPassBinding
#print AspisR1.SCC_Physical.StoredInputLaw
#print AspisR1.SCC_Physical.accepted_unassociated
#print AspisR1.F3T_Runtime.StoredCarrierBinding
#print AspisR1.CPH_Game.DeployedPairExecution
#print AspisR1.CPR_DataPersistence.TwoTransactionLaw
#print AspisR1.Rc5_Top.deployed
end AspisR1.SCC_Nonvacuity
end
