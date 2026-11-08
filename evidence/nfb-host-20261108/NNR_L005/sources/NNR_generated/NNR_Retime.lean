import NNR_ClockFree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_Retime
open Aeneas Aeneas.Std Result NNH_HostCtx
open S2W_D189Wrappers
variable {W Tx : Type}
def atSlot (c : Ctx W Tx) : Ctx W Tx :=
 {c with fixed := {c.fixed with clock := NND_Carrier.reply NND_Carrier.slot c.j.slot}}
theorem env (c : Ctx W Tx) : envOf (atSlot c) = NFB_NMFBHost.env2 c := rfl
theorem missing (c : Ctx W Tx) : missingLit (atSlot c) = missingLit c :=
 NNR_ClockFree.M1b c.sha256 c.fixed.pda _ _ c.fixed.reservation
theorem sdk_same (c : Ctx W Tx) : sdk (atSlot c) = sdk c := by
 change DrvC_Installation.sdk (FIp_Install.configuration c.fixed.indexError
  (IDa_Deployed.deployedConfiguration (missingLit (atSlot c)) c.fixed.indexError c.fixed.reservation)
  c.fixed.reservation) = _
 rw [missing c]
theorem first (c : Ctx W Tx) : model1 (atSlot c) = model1 c :=
 congrArg AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk_same c)
theorem second (c : Ctx W Tx) : model2 (atSlot c) = model2 c :=
 congrArg AdapterRw.r1_pool_adapter.owned.stage2_owned (sdk_same c)
#print axioms env
#print axioms missing
#print axioms sdk_same
#print axioms first
#print axioms second
end AspisR1.NNR_Retime
end
