import JGx_StdTX2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_StdNative
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers

/-- Exact native Result after the real validation return. emit_result's
success OR rejection remains the actual source return. -/
theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (headerBytes : Array U8 688#usize) (payload : Array U8 316#usize) (slot : S2W_ExtractionBoundary.Slot)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8
      (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value (JGx_CallerStd.value c)) err))
      CPH_Program.verifier ((JFv_World.e2 (JGx_ProofAccount.value headerBytes)).second secondSizes)
      (JGx_RequestBytes.value payload) slot=ok (.Ok JGx_Validated.value))
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    JGx_Natives.second (JGx_CallerSeed.value (JGx_CallerStd.value c)) err CPH_Program.verifier
      ((JFv_World.e2 (JGx_ProofAccount.value headerBytes)).second secondSizes)
      (JGx_RequestBytes.value payload) slot=
        (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value (JGx_CallerStd.value c)) err)).op53
          JGx_RealStatement.value := by
  apply JGx_RealNative.source (JGx_CallerStd.value c) err headerBytes _ slot _ validation realizes
  exact JGx_CallerStd.source (JGx_CallerSeed.value c) err payload
#print axioms source
end AspisR1.JGx_StdNative
end
