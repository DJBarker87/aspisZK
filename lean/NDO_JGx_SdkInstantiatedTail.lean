import NDO_JGx_SdkVerifier
import NDO_JGx_SdkEncodedTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_SdkInstantiatedTail
open Aeneas Aeneas.Std Result DrvC_Installation

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (validated : AdapterRw.r1_pool_adapter.ValidatedAsqa) (headerBytes : Array U8 688#usize)
    (common : (DrvC_Installation.sdk (JGx_Configuration.value c err)).op19=ok 1520#usize)
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    JGx_SdkEncoded.afterEncoded (DrvC_Installation.sdk (JGx_Configuration.value c err)) validated
      (JGx_ProofAccount.value headerBytes) JFx_NativeBytes.checkpoint JGx_PublicArray.value=
      (DrvC_Installation.sdk (JGx_Configuration.value c err)).op53 validated.statement :=
  JGx_SdkEncodedTail.source _ validated headerBytes common (JGx_SdkVerifier.source c err realizes)
#print axioms source
end AspisR1.JGx_SdkInstantiatedTail
end
