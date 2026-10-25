import SdkC_Accounting
import SdkC_BatchSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_BatchFixed
open Aeneas Aeneas.Std Result

/-- The native syscall parameter is phantom in the fixed batch syntax. -/
theorem current (left right : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Array U8 32#usize) :
    SdkC_BatchSource.currentCode left proof p root =
      SdkC_BatchSource.currentCode right proof p root := by
  rfl

theorem stage (left right : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize) :
    SdkC_BatchSource.stageCode left proof p root =
      SdkC_BatchSource.stageCode right proof p root := by
  rfl

#print axioms current
#print axioms stage
end AspisR1.SdkD_BatchFixed
end
