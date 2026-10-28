import NDO_JHg_RuntimeInputs
import NDO_JHb_RealSuffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHg_RealSuffix
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers
attribute [local irreducible] JHg_World.e2 JHb_World.e2 JHb_Header.account
/-- Unchanged verifier/query/batch/finish proof reused on the fixed real buffers.
The named SHA boundary remains explicit; no new combined SHA import is tried. -/
theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (JGz_Realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    JGx_SdkContinuation.afterValidation
      (sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err))
      (JHg_World.e2.second secondSizes) JGx_Validated.value=
      (sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)).op53 JGx_RealStatement.value := by
  rw [JHg_RuntimeInputs.source,←JHb_RuntimeInputs.source]
  exact JHb_RealSuffix.source c err JGz_Realizes
#print axioms source
end AspisR1.JHg_RealSuffix
end
