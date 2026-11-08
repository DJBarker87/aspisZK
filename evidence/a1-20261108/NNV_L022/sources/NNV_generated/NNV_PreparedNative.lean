import NNV_PreparedReturned
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_PreparedNative
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NNH_Run5bCtx NNV_PreparedInputs
/-- Both Rust reply arms and the exact emitted scratch writeback at canonical ports. -/
theorem returned {W Tx : Type} (c : Ctx W Tx)
 (s : RSL.Verified LIB_VLib.library) (v : LIB_VCarriers.View) (g : LIB_VCarriers.E29)
 (reply : Except LIB_VCarriers.VErr LIB_VCarriers.Prepared × LIB_VCarriers.E29)
 (events : List RSL.Event)
 (called : LIB_Prepared.child.law (s,v,g) (envOf c) ⟨.ret reply,events⟩) :
 ∃ native,
 (DrvC_Installation.currentInstalled (configuration c)).op8
  (NNV_PreparedAtHost.digest c) (sem s) (view v) () (scratch g) =
 .ok ((match native.1 with
  | .Ok p => .Ok (InstalledPreparation.currentPrepared p)
  | .Err e => .Err (InstalledPreparation.currentError e)),
  AspisR1ClaimPreparedBridge.mapArray InstalledPreparation.currentE native.2) ∧
 reply = LIBC_PreparedLaw.port native := by
 obtain ⟨native,result,port⟩ := NNV_PreparedReturned.model s v g (envOf c) reply events called
 refine ⟨native,?_,port⟩
 rw [NNV_PreparedPorts.source,result,bind_tc_ok]
 cases native
 rfl
#print axioms returned
end AspisR1.NNV_PreparedNative
end
