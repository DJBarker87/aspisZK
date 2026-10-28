import NDO_JHg_NativeAfterValidation
import JGx_SecondWrapper
import RPz8_CPH_FixtureReserve
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHg_WrapperAfterValidation
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers
/-- Conditional wrapper result. This is not the requested computed accepted2. -/
theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (magic : JGx_MagicGate.value (sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)) data=ok false)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8
      (sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err))
      CPH_Program.verifier (JHg_World.e2.second secondSizes) data slot=ok (.Ok JGx_Validated.value))
    (emitted : (sdk (JGx_Configuration.value (JGx_CallerSeed.value c) err)).op53
      JGx_RealStatement.value=ok (.Ok ()))
    (JGz_Realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    second (JGx_Natives.second (JGx_CallerSeed.value c) err) CPH_FixtureData.allocator JHg_World.e2
      CPH_Program.verifier data slot ()=ok (.Ok (JHg_World.e2.heap,())) :=
  JGx_SecondWrapper.source _ _ _ _ _ _ () () () (CPH_FixtureReserve.reserve_ok _)
    ((JHg_NativeAfterValidation.source c err data slot magic validation JGz_Realizes).trans emitted) rfl
#print axioms source
end AspisR1.JHg_WrapperAfterValidation
end
