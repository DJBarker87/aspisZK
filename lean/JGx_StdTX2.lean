import JGx_CallerStd
import JGx_TX2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_StdTX2
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers

/-- Structural request magic is computed under the selected pure std
interpretation. Actual ASQ8 validation and emit_result remain explicit. -/
theorem accepted2 {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (headerBytes : Array U8 688#usize) (payload : Array U8 316#usize) (slot : S2W_ExtractionBoundary.Slot)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8
      (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value (JGx_CallerStd.value c)) err))
      CPH_Program.verifier ((JFv_World.e2 (JGx_ProofAccount.value headerBytes)).second secondSizes)
      (JGx_RequestBytes.value payload) slot=ok (.Ok JGx_Validated.value))
    (emitted : (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value (JGx_CallerStd.value c)) err)).op53
      JGx_RealStatement.value=ok (.Ok ()))
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    S2W_D189Wrappers.second (JGx_Natives.second (JGx_CallerSeed.value (JGx_CallerStd.value c)) err)
      CPH_FixtureData.allocator (JFv_World.e2 (JGx_ProofAccount.value headerBytes)) CPH_Program.verifier
      (JGx_RequestBytes.value payload) slot ()=ok (.Ok ((JFv_World.e2 (JGx_ProofAccount.value headerBytes)).heap,())) := by
  apply JGx_TX2.accepted2 (JGx_CallerStd.value c) err headerBytes _ slot _ validation emitted realizes
  exact JGx_CallerStd.source (JGx_CallerSeed.value c) err payload
#print axioms accepted2
end AspisR1.JGx_StdTX2
end
