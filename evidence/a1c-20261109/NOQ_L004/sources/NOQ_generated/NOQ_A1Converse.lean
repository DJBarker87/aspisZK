import NOQ_A1Assembly
import NOC_Stage1Forward
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOQ_A1Converse
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_ReturnedCheckpoint

/-- Scaffold hypothesis only: the ← direction (converse) of the 345 Ok-iff, used
when the Ok clause comes from NOC_Stage1Forward.ok345. Never a shipped premise. -/
abbrev CONV (W Tx : Type) : Prop :=
 ∀ (c : NNH_HostCtx.Ctx W Tx) (program : _root_.AdapterRw.solana_pubkey.Pubkey)
 (xs : Slice _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8),
 _root_.AdapterRw.r1_pool_adapter.owned.stage1_owned (NOC_HostCtx.sdk c) program xs data = .ok (.Ok saved) →
 NNH_ReturnsBundle.tx1Value
  ⟨NND_Carrier.key program,NNH_ModelCarrier.accounts xs,NND_Carrier.bytes data⟩
  (NOC_Run5bCtx.envOf c) = .ok (NND_Carrier.bytes saved.deref)

/-- ok345's sdk (NOC_Tx1Forward.M seed at NNH_HostCtx.envOf) is the literal
corrected-host sdk: both are the fixed-clock residual of NOC_HostSeed.m0. -/
theorem sameSdk {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
 NOC_Stage1Forward.S c = NOC_HostCtx.sdk c := rfl

/-- The Ok clause from ok345, the converse from the hypothesis. -/
theorem iff_of_conv {W Tx : Type} (h : CONV W Tx) : NOQ_A1Assembly.IFF W Tx := by
 intro c program xs data saved
 refine ⟨h c program xs data saved, fun called => ?_⟩
 first
 | exact NOC_Stage1Forward.ok345 c program xs data saved called
 | (rw [← sameSdk c]; exact NOC_Stage1Forward.ok345 c program xs data saved called)

def field_of_conv {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (h : CONV W Tx) :
 RSL.TAS.NND_A1 (NOC_Run5bHost.S_host (W := W) (Tx := Tx) L0 copy std)
  NNH_Libraries.VL NNH_Libraries.P NNH_Libraries.C :=
 NOQ_A1Assembly.field_of L0 copy std (iff_of_conv h)

example {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (h : CONV W Tx) :
 type_of% (field_of_conv L0 copy std h) =
 RSL.TAS.NND_A1 (NOC_Run5bHost.S_host (W := W) (Tx := Tx) L0 copy std)
  NNH_Libraries.VL NNH_Libraries.P NNH_Libraries.C := rfl

#print axioms sameSdk
#print axioms iff_of_conv
#print axioms field_of_conv
end AspisR1.NOQ_A1Converse
end
