import CPH_FixtureVersion
import CPH_Trace
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_Nonvacuity
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState Hist_RuntimeEntry Hist_Store CPH_FixtureData
open S2W_ReturnedCheckpoint S2W_EntryWriteHistory

/-- Joint consistency of ALL new game/runtime conditions with both admitted
accepted wrappers, exact copy/load history, distinct CP cells, and nonempty
physical events. n1/n2 are explicit local witnesses, NOT source-extraction facts.
This theorem must not be advertised as inhabiting every retained CPH_Top input. -/
theorem joint_runtime (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    S2TrustedSdkBorrow (model (Nat → Record)) ∧
    S2W_TrustedStd.TrustedStd copy ∧
    Nonempty (S2W_D189Consolidation.RuntimeEntrypointAdmission (model (Nat → Record)) e1 e1.heap 3) ∧
    Nonempty (S2W_D189Consolidation.RuntimeEntrypointAdmission (model (Nat → Record)) e2 e2.heap 7) ∧
    CPH_Game.DeployedPairExecution observations false true e1 e2 saved suffix n1 n2 copy allocator id ∧
    CPR_DataPersistence.TwoTransactionLaw
      (adjacent observations) (ordinary observations (Hist_Nonvacuity.key 0#u8))
      (before observations) (tentative observations) (success observations) (loaded observations) ∧
    first n1 copy allocator e1 id data1 () = ok (.Ok (saved,CPH_FixtureWrappers.post1,())) ∧
    second n2 allocator e2 id data2 slot () = ok (.Ok (e2.heap,())) ∧
    Nonempty (S2X.CheckpointVersionBinding
      (payloadBytes encode (CPH_FixtureWrappers.post1.payload (e1.heap.accounts 2).1) 1768)
      (MultiproofConeCanonical.bytesOf (e2.buffers (e2.handles 6).1).val)) ∧
    observations.physicalEvents false ≠ [] ∧
    id = CPH_Program.verifier := by
  refine ⟨model_satisfies _,S2W_TrustedStd.specification_satisfies _,
    ⟨CPH_FixtureAdmission.admitted1⟩,⟨CPH_FixtureAdmission.admitted2⟩,
    CPH_FixtureGame.game,CPH_FixtureGame.persistence _,
    CPH_FixtureWrappers.first_success data1,CPH_FixtureWrappers.second_success data2 slot,
    ⟨CPH_FixtureVersion.version⟩,?_,rfl⟩
  rw [CPH_FixtureVersion.events]
  exact List.cons_ne_nil _ _

#print axioms joint_runtime
end AspisR1.CPH_Nonvacuity
end
