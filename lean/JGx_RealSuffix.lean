import JGx_Validated
import JGx_CallerSeed
import JGx_RuntimeInputs
import JGx_SdkInstantiatedTail
import JGx_SdkLength
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_RealSuffix
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (headerBytes : Array U8 688#usize) (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    JGx_SdkContinuation.afterValidation
      (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err))
      ((JFv_World.e2 (JGx_ProofAccount.value headerBytes)).second secondSizes) JGx_Validated.value=
      (DrvC_Installation.sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)).op53 JGx_RealStatement.value := by
  rw [JGx_RuntimeInputs.source]
  have rawLength : Slice.len (JGx_ProofAccount.value headerBytes)=58295#usize :=
    UScalar.eq_of_val_eq (JGx_ProofAccount.length headerBytes)
  rw [JGx_SdkLength.source _ _ _ _ _ JGx_Validated.proofLength rawLength (JGx_Validated.encoder _ _)]
  exact JGx_SdkInstantiatedTail.source (JGx_CallerSeed.value c) err JGx_Validated.value headerBytes
    (JGx_CallerSeed.common c err) realizes
#print axioms source
end AspisR1.JGx_RealSuffix
end
