import NOQ_WeakErrHost
import NNH_ReturnsBundle
import NNH_PhysicalCarriers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOQ_A1Assembly
open Aeneas Aeneas.Std Result AdapterRw S2Trust S2W_D189Entry S2W_ReturnedCheckpoint

/-- Scaffold hypothesis only (never a premise of the shipped field): the 345 Ok-iff
at the literal corrected-host sdk, in the shape of NOC_Stage1Iff.iff345. -/
def IFF (W Tx : Type) : Prop :=
 ∀ (c : NNH_HostCtx.Ctx W Tx) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8),
 r1_pool_adapter.owned.stage1_owned (NOC_HostCtx.sdk c) program xs data = .ok (.Ok saved) ↔
 NNH_ReturnsBundle.tx1Value
  ⟨NND_Carrier.key program,NNH_ModelCarrier.accounts xs,NND_Carrier.bytes data⟩
  (NOC_Run5bCtx.envOf c) = .ok (NND_Carrier.bytes saved.deref)

/-- Carrier map of the physical child arguments to the tx1Ok argument form. -/
theorem child1 (e : S2W_D189Entry.Entry) (p : S2W_ExtractionBoundary.Program) (data : Slice U8) :
 NNE_PhysicalAccepted.child1 NND_Carrier.error e p data =
 ⟨NND_Carrier.key p,NNH_ModelCarrier.accounts e.first,NND_Carrier.bytes data⟩ := by
 unfold NNE_PhysicalAccepted.child1
 rw [NNH_PhysicalCarriers.key,NNH_PhysicalCarriers.accounts,NNH_PhysicalCarriers.bytes]

/-- Saved-buffer carrier. -/
theorem savedBytes (saved : alloc.vec.Vec U8) : nativeBytes saved = NND_Carrier.bytes saved.deref := by
 first
 | exact NNH_PhysicalCarriers.bytes saved.deref
 | (unfold nativeBytes NND_Carrier.bytes
    apply List.map_congr_left
    intro b _
    exact NNH_PhysicalCarriers.byte b)

/-- The returned arm of the canonical 345 reference at the child arguments, in carrier form. -/
theorem returned {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (e : S2W_D189Entry.Entry)
 (p : S2W_ExtractionBoundary.Program) (data : Slice U8)
 (o : RSL.Obs (Except RSL.ProgramError RSL.Bytes)) (r : Except RSL.ProgramError RSL.Bytes)
 (ref : RSL.TX1_345.Ref NNH_Libraries.VL NNH_Libraries.P NNH_Libraries.C
   (NNE_PhysicalAccepted.child1 NND_Carrier.error e p data) (NNH_Run5bCtx.envOf c) o)
 (hret : o.exit = .ret r) :
 r = NNH_ReturnsBundle.tx1Value
  ⟨NND_Carrier.key p,NNH_ModelCarrier.accounts e.first,NND_Carrier.bytes data⟩
  (NOC_Run5bCtx.envOf c) := by
 have v := NNH_ReturnsBundle.tx1_returns _ _ o r ref hret
 rw [child1] at v
 exact v

/-- okT in the physical ModelRet1 shape (AMN.viaReturns1.okT analogue). -/
theorem okT {W Tx : Type} (h : IFF W Tx) (c : NNH_HostCtx.Ctx W Tx) (e : S2W_D189Entry.Entry)
 (p : S2W_ExtractionBoundary.Program) (data : Slice U8) (saved : alloc.vec.Vec U8)
 (v : NNH_ReturnsBundle.tx1Value
  ⟨NND_Carrier.key p,NNH_ModelCarrier.accounts e.first,NND_Carrier.bytes data⟩
  (NOC_Run5bCtx.envOf c) = .ok (nativeBytes saved)) :
 NOC_Run5bCtx.model1 c p e.first data = .ok (.Ok saved) := by
 apply (h c p e.first data saved).mpr
 rw [v, savedBytes]

/-- errT in the physical ModelRet1 shape (weak Err, by contraposition of the → direction). -/
theorem errT {W Tx : Type} (h : IFF W Tx) (c : NNH_HostCtx.Ctx W Tx) (e : S2W_D189Entry.Entry)
 (p : S2W_ExtractionBoundary.Program) (data : Slice U8) (error : RSL.ProgramError)
 (v : NNH_ReturnsBundle.tx1Value
  ⟨NND_Carrier.key p,NNH_ModelCarrier.accounts e.first,NND_Carrier.bytes data⟩
  (NOC_Run5bCtx.envOf c) = .error error) :
 ¬ ∃ saved, NOC_Run5bCtx.model1 c p e.first data = .ok (.Ok saved) := by
 rintro ⟨saved,hm⟩
 have w := (h c p e.first data saved).mp hm
 rw [v] at w
 cases w

/-- The A1 field at the corrected host, from the single scaffold hypothesis IFF.
Built directly (S_host's ModelRet1 is the NNH_AcceptanceSig.physical shape, not AMN's withMin). -/
def field_of {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (h : IFF W Tx) :
 RSL.TAS.NND_A1 (NOC_Run5bHost.S_host (W := W) (Tx := Tx) L0 copy std)
  NNH_Libraries.VL NNH_Libraries.P NNH_Libraries.C where
 stage1 := by
  intro c a env o r _hx he ref hret
  apply (NOQ_WeakErrHost.modelRet1 (W := W) (Tx := Tx) L0 copy std c a r).mpr
  intro e p data ha
  subst ha
  have he' : NNH_HostEnv.EnvRep (DGP_HostDigest.shaReply c.sha256) c.fixed.pda
   (NND_Carrier.reply NND_Carrier.slot c.j.slot) c.fixed.reservation env := he
  obtain rfl := NNH_Run5bCtx.env_unique c env he'
  have hr := returned c e p data o r ref hret
  refine ⟨fun saved hs => ?_, fun error hs => ?_⟩
  · exact okT h c e p data saved (hr.symm.trans hs)
  · exact errT h c e p data error (hr.symm.trans hs)

example {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (h : IFF W Tx) :
 type_of% (field_of L0 copy std h) =
 RSL.TAS.NND_A1 (NOC_Run5bHost.S_host (W := W) (Tx := Tx) L0 copy std)
  NNH_Libraries.VL NNH_Libraries.P NNH_Libraries.C := rfl

#print axioms child1
#print axioms savedBytes
#print axioms returned
#print axioms okT
#print axioms errT
#print axioms field_of
end AspisR1.NOQ_A1Assembly
end
