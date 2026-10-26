import SCE_FixtureVersion
import SCE_FixtureSubmission
import SCE_Projection
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_Nonvacuity
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState Hist_RuntimeEntry Hist_Store SCE_FixtureData
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment F3T_ByteCarrier

/-- SAME fixture entries inhabit BOTH admissions, BOTH local native wrapper
successes, all approved game clauses, persistence, and nonempty physical
checkpoint actions, while submitting JFx proof/public bytes. The zero-filled
Pool prefix and local n1/n2 are deliberate model witnesses, not installed
crypto/source acceptance. No extraction law for these natives is assumed. -/
theorem joint (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (H : Bytes → State) :
    S2TrustedSdkBorrow (model (Nat → Record)) ∧
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
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : Submission) := by
  refine ⟨model_satisfies _,S2W_TrustedStd.specification_satisfies _,
    ⟨SCE_FixtureAdmission.admitted1⟩,⟨SCE_FixtureAdmission.admitted2⟩,
    SCE_FixtureGame.game,SCE_FixtureGame.persistence _,
    SCE_FixtureWrappers.first_success data1,SCE_FixtureWrappers.second_success data2 slot,
    ⟨SCE_FixtureVersion.version⟩,?_,SCE_FixtureSubmission.original_submission data1 data2 slot H⟩
  rw [SCE_FixtureVersion.events]
  exact List.cons_ne_nil _ _

#print axioms joint
end AspisR1.SCE_Nonvacuity
end
