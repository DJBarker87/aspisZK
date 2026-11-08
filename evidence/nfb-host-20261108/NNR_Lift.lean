import NNR_CommonTransport
import NNR_OuterBuild
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_Lift
open Aeneas Aeneas.Std Result VTop_Stages NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NNH_NativeOracleSlots

theorem M2 : NFB_NMFBHost.M2 := by
 intro H pda k r pub proof ck records events domain native
 obtain ⟨v,parser,child⟩ := NNR_OuterInvert.accepted _ _ _ _ native
 obtain ⟨rs,transported,_⟩ := NNR_CommonTransport.accepted H pda k r
  (LIBB_PartitionEnv.digest (DGP_HostDigest.envInst H pda k r)) () pub proof ck
  domain.proofExtent (.Ok ()) records child
 let frame : Frame Unit Unit :=
  ⟨⟨LIBB_PartitionEnv.digest (DGP_HostDigest.envInst H pda k r),pub,proof,ck,()⟩,NNH_064Install.frame⟩
 obtain ⟨ev,built⟩ := NNR_OuterBuild.accepted H frame v parser rs transported
 exact ⟨rs,ev,built⟩
#print axioms M2
end AspisR1.NNR_Lift
end
