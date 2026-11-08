import NNH_Run5bPreparedSlot
import LIBC_PreparedLog
import LIBC_PreparedErrors
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bPreparedModel
open Aeneas Aeneas.Std Result NNH_Run5bCtx
open AspisR1CurrentCaller

theorem source {W Tx : Type} (c : Ctx W Tx) (D : aspis_core.digest.Digest32 Unit)
 (sem : r1_semantic.Verified Unit) (v : verifier.View)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
 (DrvC_Installation.currentInstalled (configuration c)).op8 D sem v () g =
 (do let (reply,scratch) ← NGN_Emitted.prepared NHL_PreparedScalars.actual
       (InstalledPreparation.retainedDigest D) (InstalledPreparation.retainedSem sem)
       (InstalledPreparation.retainedView v) ()
       (AspisR1ClaimPreparedBridge.mapArray InstalledPreparation.retainedE g)
     .ok ((match reply with
       | .Ok p => .Ok (InstalledPreparation.currentPrepared p)
       | .Err e => .Err (InstalledPreparation.currentError e)),
       AspisR1ClaimPreparedBridge.mapArray InstalledPreparation.currentE scratch)) := by
 rw [NNH_Run5bPreparedSlot.fixed c D sem v () g]
 rw [←BorrowedClaimPrepared.closedPreparationCode_installed]
 unfold BorrowedClaimPrepared.closedPreparationCode
 rw [AspisR1PublicPreparation.PreparedHashCode.erase_bind,
  AspisR1PublicPreparation.PreparedHashCode.preparation_erasure,
  BorrowedClaimPrepared.closedHashBoundaries_queries,
  AspisR1PublicPreparation.OriginalPreparedNative.eq_prepare,
  LIBC_PreparedLog.installation,LIBC_PreparedErrors.complete]
 rfl
#print axioms source
end AspisR1.NNH_Run5bPreparedModel
end
