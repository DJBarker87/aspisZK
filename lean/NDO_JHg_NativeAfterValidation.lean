import NDO_JHg_RealSuffix
import JGx_SdkAfterValidationEq
import NDO_JGx_Natives
import JGx_MagicGate
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHg_NativeAfterValidation
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers
attribute [local irreducible] JHg_World.e2 JHb_Header.account
/-- Split after the actual validation return. Successful validation remains
explicit; this does not claim authentication or reconstruction was computed. -/
theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (magic : JGx_MagicGate.value (sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)) data=ok false)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8
      (sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err))
      CPH_Program.verifier (JHg_World.e2.second secondSizes) data slot=ok (.Ok JGx_Validated.value))
    (JGz_Realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    JGx_Natives.second (JGx_CallerSeed.value c) err CPH_Program.verifier
      (JHg_World.e2.second secondSizes) data slot=
      (sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)).op53 JGx_RealStatement.value :=
  (JGx_SdkAfterValidationEq.source _ CPH_Program.verifier _ data slot JGx_Validated.value
    (JGx_EntryReads.count _) magic validation).trans (JHg_RealSuffix.source c err JGz_Realizes)
#print axioms source
end AspisR1.JHg_NativeAfterValidation
end
