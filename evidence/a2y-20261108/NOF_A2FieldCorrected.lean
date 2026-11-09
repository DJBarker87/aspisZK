import NOF_A2Field
import NOC_Run5bHost
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOF_A2FieldCorrected
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Seed-generic clock independence of the selected residual (proof pattern of
NNR_ClockFree.M1b, restated for an arbitrary seed). -/
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

/-- NOC analogue of NNH_Run5bCtx.missing_at_slot / NOF_A2Field.sdk_at_slot. -/
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

/-- A2 at the corrected host (NOC_HostSeed.m0: current op1 installed). Same proof
as NOF_A2Field.field; every reused theorem is seed-generic. -/
def field {W Tx : Type} (L0 : _) (copy : _) (std : _) :
 RSL.TAS.NND_A2 (AspisR1.NOC_Run5bHost.S_host (W := W) (Tx := Tx) L0 copy std)
  NNH_Libraries.L NNH_Libraries.D NNH_Libraries.V0 where
 stage2 := by
  intro c a env o r _hx he ref hret hsel hr
  subst hr
  subst hsel
  have he' : NNH_HostEnv.EnvRep (DGP_HostDigest.shaReply c.sha256) c.fixed.pda
   (NND_Carrier.reply NND_Carrier.slot c.j.slot) c.fixed.reservation env := he
  obtain rfl := NNH_Run5bCtx.env_unique c env he'
  have rep := NOF_A2Field.reserved_at c he'.2.2.2
  have ref' : RSL.TX2_241.Ref NNH_Libraries.L NNH_Libraries.D NNH_Libraries.V0
    ⟨NND_Carrier.key CPH_Program.verifier,
     NNH_ModelCarrier.accounts (c.j.entry.second S2W_D189Wrappers.secondSizes),
     NND_Carrier.bytes c.j.data, NND_Carrier.reply NND_Carrier.slot c.j.slot⟩
    (NNH_Run5bCtx.envOf c) o := by
   rw [← NNH_PhysicalCarriers.key,← NNH_PhysicalCarriers.accounts,← NNH_PhysicalCarriers.bytes]
   exact ref
  obtain ⟨p,segment,domain,auth,iff⟩ := NNY_Stage2PacketResidual.returned
   (NOC_HostSeed.m0 (NNH_HostCtx.envOf c).reservation)
   (NNH_Run5bCtx.envOf c) c.fixed.indexError c.fixed.reservation CPH_Program.verifier
   (c.j.entry.second S2W_D189Wrappers.secondSizes) c.j.data c.j.slot o ref' hret
  have op := iff.mpr (NOF_Tx2Op11.tx2Op11 (NOC_HostSeed.m0 (NNH_HostCtx.envOf c).reservation)
   (NNH_Run5bCtx.envOf c) c.fixed.indexError c.fixed.reservation rep p.encoded.to_slice segment
   p.checkpoint domain auth)
  rw [sdk_at_slot] at op
  exact op

example {W Tx : Type} (L0 : _) (copy : _) (std : _) :
 type_of% (field (W := W) (Tx := Tx) L0 copy std) =
 RSL.TAS.NND_A2 (AspisR1.NOC_Run5bHost.S_host (W := W) (Tx := Tx) L0 copy std)
  NNH_Libraries.L NNH_Libraries.D NNH_Libraries.V0 := rfl

#print axioms clockFree
#print axioms sdk_at_slot
#print axioms field
end AspisR1.NOF_A2FieldCorrected
end
