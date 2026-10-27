import ARS_GameLoss
import ARS_CoverageClass
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_GameLossJoint
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open CPG_Projection CPH_FixtureData

/-- Joint diagnostic under the approved game/runtime interfaces. Failed native
syscalls have no returned digest, so returning-value agreement alone cannot
exclude them. This is NOT joint non-vacuity of Rc10's extraction/finish premises. -/
theorem permitted (H : Bytes → State) (parts : SdkC_Source.Parts)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    CPH_Game.DeployedPairExecution observations false true e1 e2 saved suffix
      n1 (ARS_GameLoss.rejecting parts) copy allocator id ∧
    CPR_DataPersistence.TwoTransactionLaw
      (adjacent observations) (ordinary observations (Hist_Nonvacuity.key 0#u8))
      (before observations) (tentative observations) (success observations) (loaded observations) ∧
    S2W_D189Consolidation.RuntimeEntrypointAdmission (model (Nat → Record)) e1 e1.heap 3 ∧
    S2W_D189Consolidation.RuntimeEntrypointAdmission (model (Nat → Record)) e2 e2.heap 7 ∧
    first n1 copy allocator e1 id data () = ok (.Ok (saved,CPH_FixtureWrappers.post1,())) ∧
    second (ARS_GameLoss.rejecting parts) allocator e2 id data slot () = .fail .assertionFailure ∧
    S2W_ExtractionBoundary.P1 H H ∧
    S2W_ExtractionBoundary.RuntimeSyscall SCG_PartialOracle.failingOracle H ∧
    ARS_QueryTransport.Agrees H
      (SdkC_Source.run SCG_PartialOracle.failingOracle (SdkC_Source.digestCode parts) []).2 ∧
    (SdkC_Source.run SCG_PartialOracle.failingOracle (SdkC_Source.digestCode parts) []).1 ≠
      (eval H (SdkC_Oracle.program (SdkC_Source.digestCode parts))).2 := by
  refine ⟨ARS_GameLoss.allowed parts,CPH_FixtureGame.persistence _,CPH_FixtureAdmission.admitted1,
    CPH_FixtureAdmission.admitted2,CPH_FixtureWrappers.first_success data,ARS_GameLoss.rejects parts data slot,
    SCG_PartialOracle.realization H,SCG_PartialOracle.syscall H,?_,(ARR_OracleLoss.digest_loss H parts).2.2⟩
  intro q member digest returned
  rw [SdkC_Source.digest_trace] at member
  simp only [List.nil_append] at member
  obtain rfl := List.mem_singleton.mp member
  cases returned

#print axioms permitted
end AspisR1.ARS_GameLossJoint
end
