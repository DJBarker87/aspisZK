import JFv_WorldBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_RuntimeWitness
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open JFv_World CPG_Projection CPP_BankState Hist_RuntimeEntry

theorem compatible (proofAccount : Slice U8) (n1 : S2W_ExtractionBoundary.First)
    (n2 : S2W_ExtractionBoundary.Second) :
    S2TrustedSdkBorrow (model (Nat → Record)) ∧
    S2W_TrustedStd.TrustedStd CPH_FixtureData.copy ∧
    S2W_D189Consolidation.RuntimeEntrypointAdmission
      (model (Nat → Record)) (e1 proofAccount) (e1 proofAccount).heap 3 ∧
    S2W_D189Consolidation.RuntimeEntrypointAdmission
      (model (Nat → Record)) (e2 proofAccount) (e2 proofAccount).heap 7 ∧
    CPH_Game.DeployedPairExecution (observations proofAccount) false true
      (e1 proofAccount) (e2 proofAccount) saved [] n1 n2 CPH_FixtureData.copy
      CPH_FixtureData.allocator CPH_Program.verifier ∧
    CPR_DataPersistence.TwoTransactionLaw
      (adjacent (observations proofAccount))
      (ordinary (observations proofAccount) (Hist_Nonvacuity.key 0#u8))
      (before (observations proofAccount)) (tentative (observations proofAccount))
      (success (observations proofAccount)) (loaded (observations proofAccount)) :=
  ⟨JFv_WorldAdmission.trusted.1,JFv_WorldAdmission.trusted.2,
    JFv_WorldAdmission.first proofAccount,JFv_WorldAdmission.second proofAccount,
    JFv_World.game proofAccount n1 n2,JFv_World.persistence proofAccount _⟩

#print axioms compatible
end AspisR1.JFv_RuntimeWitness
end
