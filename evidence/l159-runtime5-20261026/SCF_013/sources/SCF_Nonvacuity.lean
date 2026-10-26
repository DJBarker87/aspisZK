import SCE_FixtureBudget
import SCF_Charge
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCF_Nonvacuity
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState Hist_RuntimeEntry Hist_Store SCE_FixtureData
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment F3T_ByteCarrier
/-- Same game, admissions, native successes, persistence AND actual observer
bytes simultaneously. Source acceptance is deliberately left as computed. -/
theorem joint {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (H : Bytes → State)
    (project : GExq_AccountExperiment.Outcome Unit → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : GExq_AccountExperiment.Outcome Unit → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    (
    (S2TrustedSdkBorrow (model (Nat → Record)) ∧
    S2W_TrustedStd.TrustedStd copy ∧
    Nonempty (S2W_D189Consolidation.RuntimeEntrypointAdmission (model (Nat → Record)) e1 e1.heap 3) ∧
    Nonempty (S2W_D189Consolidation.RuntimeEntrypointAdmission (model (Nat → Record)) e2 e2.heap 7) ∧
    CPH_Game.DeployedPairExecution observations false true e1 e2 saved suffix n1 n2 copy allocator id ∧
    CPR_DataPersistence.TwoTransactionLaw
      (adjacent observations) (ordinary observations (Hist_Nonvacuity.key 0#u8))
      (before observations) (tentative observations) (success observations) (loaded observations) ∧
    first n1 copy allocator e1 id data1 () = ok (.Ok (saved,SCE_FixtureWrappers.post1,())) ∧
    second n2 allocator e2 id data2 slot () = ok (.Ok (e2.heap,())) ∧
    Nonempty (S2X.CheckpointVersionBinding
      (S2W_EntryWriteHistory.payloadBytes S2W_ReturnedCheckpoint.encode
        (SCE_FixtureWrappers.post1.payload (e1.heap.accounts 2).1) 1768)
      (MultiproofConeCanonical.bytesOf (e2.buffers (e2.handles 6).1).val)) ∧
    observations.physicalEvents false ≠ [] ∧
    (eval H (submission (SCE_FixtureSubmission.adversary data1 data2 slot))).2 =
      (⟨MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes,
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : Submission)) ∧
    (∃ run : RunView,
      (eval H (runtime c hashv copy allocator id
        (SCE_FixtureSubmission.adversary data1 data2 slot))).2 = some run ∧
      run.2.1.stored = MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes ∧
      run.2.1.physical.bytes = MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes)) ∧
    (∀ world, (eval world (account c hashv copy allocator id
      (SCE_FixtureSubmission.adversary data1 data2 slot))).1.length ≤ 1921) ∧
    F3T_AccountCharge.mass (account c hashv copy allocator id
      (SCE_FixtureSubmission.adversary data1 data2 slot)) project select 0 ≤
      F3T_Numeric.accountLoss 0 := by
  have budget := SCE_FixtureBudget.zero data1 data2 slot
  have charge := SCF_Charge.charged c hashv copy allocator id
    (SCE_FixtureSubmission.adversary data1 data2 slot) 0 0 budget.1 budget.2 project select
  exact ⟨SCE_JointObserver.joint c hashv data1 data2 slot H, charge.1, charge.2.2⟩

#print axioms joint
end AspisR1.SCF_Nonvacuity
end
