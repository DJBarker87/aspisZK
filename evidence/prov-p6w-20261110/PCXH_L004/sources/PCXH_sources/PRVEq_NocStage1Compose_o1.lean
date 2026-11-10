import PRVEq_AdapterStage1DeployedNOC_o1
import NOC_Stage1Iff
set_option autoImplicit false
noncomputable section
/-! PCVP_ composition at the corrected seed: the fresh frozen stage1_owned (PCVK_S1_o1, 4bb3b3f emission) at the
headline's sdk is Ok-equivalent to the library tx1Value, by PCVP_S1.noc_model1 (fresh = model1 c) and the existing
NOC_Stage1Iff.iff345 (forward NOC_Stage1Forward.ok345, converse NOC_Stage1Conv.conv).
Conditional only on what noc_model1 uses: the Stage1 Bound fields instantiated by the deployed sdk ops (rfl, organisation).
Domain: every program/xs/data/saved (iff345 has no domain hypothesis). Seed: NOC_HostSeed.m0 via NOC_HostCtx.sdk c. -/
namespace AspisR1.PCVP_S1Compose
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NNH_ModelCarrier

theorem fresh_stage1_iff {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : _root_.AdapterRw.solana_pubkey.Pubkey)
    (xs : Slice _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8) :
    _root_.AdapterRw.PCVK_S1_o1.r1_pool_adapter.owned.stage1_owned (PCVP_S1.xOf (NOC_HostCtx.sdk c)) program xs data = .ok (.Ok saved) ↔
    NNH_ReturnsBundle.tx1Value ⟨key program, accounts xs, bytes data⟩ (NOC_Run5bCtx.envOf c) =
      .ok (bytes saved.deref) := by
  rw [PCVP_S1.noc_model1 c]
  exact NOC_Stage1Iff.iff345 c program xs data saved

#print axioms fresh_stage1_iff
end AspisR1.PCVP_S1Compose
end
