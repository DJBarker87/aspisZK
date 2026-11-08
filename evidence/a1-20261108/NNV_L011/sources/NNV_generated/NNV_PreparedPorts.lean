import NNV_PreparedInputs
import NNV_PreparedAtHost
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_PreparedPorts
open Aeneas Aeneas.Std Result NNH_Run5bCtx AspisR1CurrentCaller
open NNV_PreparedInputs
/-- Full Result at all three canonical input ports; no returned/success premise. -/
theorem source {W Tx : Type} (c : Ctx W Tx)
 (s : RSL.Verified LIB_VLib.library) (v : LIB_VCarriers.View) (g : LIB_VCarriers.E29) :
 (DrvC_Installation.currentInstalled (configuration c)).op8
  (NNV_PreparedAtHost.digest c) (sem s) (view v) () (scratch g) =
 (do let (reply,out) ← NGN_Emitted.prepared NHL_PreparedScalars.actual
      (LIBC_PreparedLog.digest (envOf c))
      (LIBC_PreparedCarriers.verified LIB_Prepared.types s) v () g
     .ok ((match reply with
       | .Ok p => .Ok (InstalledPreparation.currentPrepared p)
       | .Err e => .Err (InstalledPreparation.currentError e)),
       AspisR1ClaimPreparedBridge.mapArray InstalledPreparation.currentE out)) := by
 rw [NNV_PreparedAtHost.source,semantic,view_input,scratch_input]
 rfl
#print axioms source
end AspisR1.NNV_PreparedPorts
end
