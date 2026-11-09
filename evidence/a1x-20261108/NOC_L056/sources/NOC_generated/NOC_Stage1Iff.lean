import NOC_Stage1Conv
import NNR_ClockFree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_Stage1Iff
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NNH_ModelCarrier
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Restated from NOF_A2FieldCorrected.clockFree (seed-generic clock
independence of the selected residual), to avoid importing the a2 overlay. -/
theorem clockFree (H : Bytes → State)
 (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32) (k k' : Except RSL.ProgramError UInt64)
 (r : NP6_StdModel.Reservation) (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) :
 NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m (DGP_HostDigest.envInst H pda k r))
  (DGP_HostDigest.envInst H pda k r) =
 NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m (DGP_HostDigest.envInst H pda k' r))
  (DGP_HostDigest.envInst H pda k' r) := by
 rw [NNR_ClockFree.residual H pda k k' r m]
 unfold NNH_Tx2Configuration.select
 rw [NNR_ClockFree.modelSlots H pda k k' r]
 try rfl

/-- Restated from NOF_A2FieldCorrected.sdk_at_slot. -/
theorem sdk_at_slot {W Tx : Type} (c : NOC_Run5bCtx.Ctx W Tx) :
 NNH_CorrectConfiguration.sdk (NOC_HostSeed.m0 (NNH_HostCtx.envOf c).reservation)
  (NOC_Run5bCtx.envOf c) c.fixed.indexError c.fixed.reservation = NOC_HostCtx.sdk c := by
 show DrvC_Installation.sdk (FIp_Install.configuration c.fixed.indexError
  (IDa_Deployed.deployedConfiguration (NNH_Tx2Configuration.select
   (NNH_CorrectConfiguration.residual (NOC_HostSeed.m0 (NNH_HostCtx.envOf c).reservation)
    (DGP_HostDigest.envInst c.sha256 c.fixed.pda (NND_Carrier.reply NND_Carrier.slot c.j.slot)
     c.fixed.reservation))
   (DGP_HostDigest.envInst c.sha256 c.fixed.pda (NND_Carrier.reply NND_Carrier.slot c.j.slot)
     c.fixed.reservation)) c.fixed.indexError c.fixed.reservation) c.fixed.reservation) = _
 rw [clockFree c.sha256 c.fixed.pda (NND_Carrier.reply NND_Carrier.slot c.j.slot) c.fixed.clock
  c.fixed.reservation]

theorem sameSdk {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) : NOC_Stage1Forward.S c = NOC_HostCtx.sdk c :=
 sdk_at_slot c

/-- The 345 Ok-iff at the literal S_host model1 sdk (NOC_HostCtx.sdk c):
forward NOC_Stage1Forward.ok345, converse NOC_Stage1Conv.conv. -/
theorem iff345 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8) :
 r1_pool_adapter.owned.stage1_owned (NOC_HostCtx.sdk c) program xs data = .ok (.Ok saved) ↔
 NNH_ReturnsBundle.tx1Value ⟨key program,accounts xs,bytes data⟩ (NOC_Run5bCtx.envOf c) =
  .ok (bytes saved.deref) := by
 rw [← sameSdk c]
 exact ⟨NOC_Stage1Conv.conv c program xs data saved, NOC_Stage1Forward.ok345 c program xs data saved⟩

#print axioms clockFree
#print axioms sdk_at_slot
#print axioms sameSdk
#print axioms iff345
end AspisR1.NOC_Stage1Iff
end
