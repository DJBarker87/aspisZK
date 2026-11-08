import NNV_PreparedAtHost
import NNV_PreparedInputs
import LIB_Prepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_PreparedValue
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NNH_Run5bCtx
/-- Returned evaluator success selects the SAME emitted P reply and scratch.
No separate graph witness or child-domain hypothesis is introduced. -/
theorem source {W Tx : Type} (c : Ctx W Tx)
 (sem : RSL.Verified LIB_VLib.library) (v : LIB_VCarriers.View)
 (g after : LIB_VCarriers.E29) (p : LIB_VCarriers.Prepared)
 (called : LIB_Prepared.value (sem,v,g) (envOf c) = (.ok p,after)) :
 (DrvC_Installation.currentInstalled (configuration c)).op8 (NNV_PreparedAtHost.digest c)
  (NNV_PreparedInputs.sem sem) (NNV_PreparedInputs.view v) () (NNV_PreparedInputs.scratch g) =
 .ok (.Ok (InstalledPreparation.currentPrepared p),NNV_PreparedInputs.scratch after) := by
 have reflected : NGN_Emitted.prepared NHL_PreparedScalars.actual
  (LIBC_PreparedLog.digest (envOf c))
  (LIBC_PreparedCarriers.verified LIB_Prepared.types sem) v () g = .ok (.Ok p,after) := by
  change LIBC_PreparedLaw.value (LIB_Prepared.input (sem,v,g)) (envOf c) = (.ok p,after) at called
  unfold LIBC_PreparedLaw.value at called
  rw [LIBC_PreparedLaw.native_result] at called
  cases native : NGN_Emitted.prepared NHL_PreparedScalars.actual
   (LIBC_PreparedLog.digest (envOf c))
   (LIBC_PreparedCarriers.verified LIB_Prepared.types sem) v () g with
  | fail e => rw [native] at called;cases called
  | div => rw [native] at called;cases called
  | ok pair =>
   rcases pair with ⟨reply,scratch⟩
   cases reply with
   | Err e => rw [native] at called;cases called
   | Ok prepared =>
    rw [native] at called
    cases called
    exact native
 rw [NNV_PreparedAtHost.source,reflected,bind_tc_ok]
 rfl
#print axioms source
end AspisR1.NNX_PreparedValue
end
