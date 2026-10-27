import JGx_RealNative
import JGx_SecondWrapper
import CPH_FixtureReserve
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_TX2
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers

/-- Conditional wrapper on the actual extracted second native and retained
checkpoint. The three named SDK-prefix/emission observations are NOT yet
computed facts; this is not a closed accepted2 fixture or top discharge. -/
theorem accepted2 {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (headerBytes : Array U8 688#usize) (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (magic : JGx_MagicGate.value
      (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)) data=ok false)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8
      (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err))
      CPH_Program.verifier ((JFv_World.e2 (JGx_ProofAccount.value headerBytes)).second secondSizes) data slot=
        ok (.Ok JGx_Validated.value))
    (emitted : (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)).op53
      JGx_RealStatement.value=ok (.Ok ()))
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    S2W_D189Wrappers.second (JGx_Natives.second (JGx_CallerSeed.value c) err) CPH_FixtureData.allocator
      (JFv_World.e2 (JGx_ProofAccount.value headerBytes)) CPH_Program.verifier data slot ()=
        ok (.Ok ((JFv_World.e2 (JGx_ProofAccount.value headerBytes)).heap,())) :=
  JGx_SecondWrapper.source _ _ _ CPH_Program.verifier data slot () () ()
    (CPH_FixtureReserve.reserve_ok _) ((JGx_RealNative.source c err headerBytes data slot magic validation realizes).trans emitted) rfl
#print axioms accepted2
end AspisR1.JGx_TX2
end
