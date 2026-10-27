import JHg_WrapperAfterValidation
import JHi_Configuration
import JHi_SHARealization
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHi_TX2
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers

def seed {C : Type} (c : Configuration FIo_Install.W C) :=
  JHf_Configuration.select (JHi_Configuration.base c)

/-- Conditional second-wrapper result. It deliberately retains actual
validation; this is not the requested SHA-only accepted2. -/
theorem after_validation {C : Type} (c : Configuration FIo_Install.W C) (err : C) (slot : U64)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8
      (sdk (JHi_Configuration.value c err)) CPH_Program.verifier
      (JHg_World.e2.second secondSizes) JHb_DataRequest.value (.Ok slot)=ok (.Ok JGx_Validated.value))
    (sha : JHi_SHARealization.SHARealization) :
    second (JGx_Natives.second (JGx_CallerSeed.value (seed c)) err) CPH_FixtureData.allocator
      JHg_World.e2 CPH_Program.verifier JHb_DataRequest.value (.Ok slot) ()=
        ok (.Ok (JHg_World.e2.heap,())) :=
  JHg_WrapperAfterValidation.source (seed c) err JHb_DataRequest.value (.Ok slot)
    (JHi_Configuration.magic c err) validation (JHi_Configuration.emission_model c err)
    (JHi_SHARealization.realizes sha)
#print axioms after_validation
end AspisR1.JHi_TX2
end
