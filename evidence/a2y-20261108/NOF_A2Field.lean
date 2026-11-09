import NOF_Tx2Op11
import NNY_Stage2PacketResidual
import NNH_Run5bHost
import NNH_PhysicalCarriers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOF_A2Field
open Aeneas Aeneas.Std Result

/-- The installed host SDK at the TX2 slot environment is the corrected SDK at
the host seed: the residual selected at the slot clock is the literal missing
binder (NNH_Run5bCtx.missing_at_slot). -/
theorem sdk_at_slot {W Tx : Type} (c : NNH_Run5bCtx.Ctx W Tx) :
 NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 (NNH_Run5bCtx.envOf c) c.fixed.indexError
  c.fixed.reservation = NNH_HostCtx.sdk c := by
 show DrvC_Installation.sdk (FIp_Install.configuration c.fixed.indexError
  (IDa_Deployed.deployedConfiguration (NNH_Tx2Configuration.select
   (NNH_CorrectConfiguration.residual NNH_HostSeed.m0 (NNH_Run5bCtx.envOf c))
   (NNH_Run5bCtx.envOf c)) c.fixed.indexError c.fixed.reservation) c.fixed.reservation) = _
 rw [NNH_Run5bCtx.missing_at_slot]

/-- The headline reservation binder and the TX2 environment reply agree. -/
theorem reserved_at {W Tx : Type} (c : NNH_Run5bCtx.Ctx W Tx)
 (iff0 : (NNH_Run5bCtx.envOf c).reservation = true ↔ c.fixed.reservation = .Ok ()) :
 NJC_FilledClause.reserved c.fixed.reservation = (NNH_Run5bCtx.envOf c).reservation := by
 revert iff0
 cases c.fixed.reservation with
 | Ok u =>
  cases u
  intro iff0
  exact (iff0.mpr rfl).symm
 | Err e =>
  intro iff0
  cases hb : (NNH_Run5bCtx.envOf c).reservation
  · rfl
  · exact absurd (iff0.mp hb) (fun h => by cases h)

/-- Y4: the A2 model-transport field at the corrected host. For every context,
environment agreeing with the host runtime, and returned-Ok observation of the
canonical RSL 241 reference at the selected TX2 child arguments, the installed
model2 (`stage2_owned (sdk c)`) returns Ok. Adversary/context universal; no
Root0, Realizes, success, representation, selector or hash-injectivity premise. -/
def field {W Tx : Type} (L0 : _) (copy : _) (std : _) :
 RSL.TAS.NND_A2 (AspisR1.NNH_Run5bHost.S_host (W := W) (Tx := Tx) L0 copy std)
  NNH_Libraries.L NNH_Libraries.D NNH_Libraries.V0 where
 stage2 := by
  intro c a env o r _hx he ref hret hsel hr
  subst hr
  subst hsel
  have he' : NNH_HostEnv.EnvRep (DGP_HostDigest.shaReply c.sha256) c.fixed.pda
   (NND_Carrier.reply NND_Carrier.slot c.j.slot) c.fixed.reservation env := he
  obtain rfl := NNH_Run5bCtx.env_unique c env he'
  have rep := reserved_at c he'.2.2.2
  have ref' : RSL.TX2_241.Ref NNH_Libraries.L NNH_Libraries.D NNH_Libraries.V0
    ⟨NND_Carrier.key CPH_Program.verifier,
     NNH_ModelCarrier.accounts (c.j.entry.second S2W_D189Wrappers.secondSizes),
     NND_Carrier.bytes c.j.data, NND_Carrier.reply NND_Carrier.slot c.j.slot⟩
    (NNH_Run5bCtx.envOf c) o := by
   rw [← NNH_PhysicalCarriers.key,← NNH_PhysicalCarriers.accounts,← NNH_PhysicalCarriers.bytes]
   exact ref
  obtain ⟨p,segment,domain,auth,iff⟩ := NNY_Stage2PacketResidual.returned NNH_HostSeed.m0
   (NNH_Run5bCtx.envOf c) c.fixed.indexError c.fixed.reservation CPH_Program.verifier
   (c.j.entry.second S2W_D189Wrappers.secondSizes) c.j.data c.j.slot o ref' hret
  have op := iff.mpr (NOF_Tx2Op11.tx2Op11 NNH_HostSeed.m0 (NNH_Run5bCtx.envOf c)
   c.fixed.indexError c.fixed.reservation rep p.encoded.to_slice segment p.checkpoint domain auth)
  rw [sdk_at_slot] at op
  exact op

example {W Tx : Type} (L0 : _) (copy : _) (std : _) :
 type_of% (field (W := W) (Tx := Tx) L0 copy std) =
 RSL.TAS.NND_A2 (AspisR1.NNH_Run5bHost.S_host (W := W) (Tx := Tx) L0 copy std)
  NNH_Libraries.L NNH_Libraries.D NNH_Libraries.V0 := rfl

#print axioms sdk_at_slot
#print axioms reserved_at
#print axioms field
end AspisR1.NOF_A2Field
end
