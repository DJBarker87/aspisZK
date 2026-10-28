import NDO_JGx_Validated
import NDO_JGx_CallerSeed
import NDO_JHb_RuntimeInputs
import NDO_JGx_SdkInstantiatedTail
import JGx_SdkLength
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_RealSuffix
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers
attribute [local irreducible] JHb_World.e2 JHb_Header.account JHb_Header.value

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    JGx_SdkContinuation.afterValidation
      (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err))
      (JHb_World.e2.second secondSizes) JGx_Validated.value=
      (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)).op53 JGx_RealStatement.value := by
  rw [JHb_RuntimeInputs.source]
  have rawLength : Slice.len JHb_Header.account=58295#usize :=
    UScalar.eq_of_val_eq JHb_Header.length
  rw [JGx_SdkLength.source _ _ _ _ _ JGx_Validated.proofLength rawLength (JGx_Validated.encoder _ _)]
  simpa only [JHb_Header.account,JGx_Validated.value] using JGx_SdkInstantiatedTail.source (JGx_CallerSeed.value c) err JGx_Validated.value JHb_Header.value
    (JGx_CallerSeed.common c err) realizes
#print axioms source
end AspisR1.JHb_RealSuffix
end
