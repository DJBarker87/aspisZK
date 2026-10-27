import JGx_RealSuffix
import JGx_MagicGate
import JGx_Natives
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_RealNative
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (headerBytes : Array U8 688#usize) (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (magic : JGx_MagicGate.value
      (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)) data=ok false)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8
      (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err))
      CPH_Program.verifier ((JFv_World.e2 (JGx_ProofAccount.value headerBytes)).second secondSizes) data slot=
        ok (.Ok JGx_Validated.value))
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    JGx_Natives.second (JGx_CallerSeed.value c) err CPH_Program.verifier
      ((JFv_World.e2 (JGx_ProofAccount.value headerBytes)).second secondSizes) data slot=
      (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)).op53 JGx_RealStatement.value :=
  (JGx_SdkAfterValidationEq.source _ CPH_Program.verifier _ data slot JGx_Validated.value
    (JGx_EntryReads.count _) magic validation).trans (JGx_RealSuffix.source c err headerBytes realizes)
#print axioms source
end AspisR1.JGx_RealNative
end
