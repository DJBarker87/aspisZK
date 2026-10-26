import RPz7_SdkD_BatchLoopFixed
import RPz7_SdkC_BatchSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_BatchFixed
open Aeneas Aeneas.Std Result

theorem values (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D E : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize)
    (roots : Array SdkC_Source.Digest 3#usize) (which : Usize) :
    Port9OR_Batch.values base D hash proof queries roots which =
      Port9OR_Batch.values base E hash proof queries roots which := by
  simp only [Port9OR_Batch.values,SdkD_BatchLoopFixed.tree base D E]

/-- The native syscall parameter is phantom in the fixed batch syntax. -/
theorem current (left right : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Array U8 32#usize) :
    SdkC_BatchSource.currentCode left proof p root =
      SdkC_BatchSource.currentCode right proof p root := by
  simp only [SdkC_BatchSource.currentCode,SdkC_BatchSource.stageCode,
    SdkC_BatchSource.code,values Port4B_Install.leaves (SdkC_Source.dictionary left) (SdkC_Source.dictionary right)]

theorem stage (left right : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize) :
    SdkC_BatchSource.stageCode left proof p root =
      SdkC_BatchSource.stageCode right proof p root := by
  simp only [SdkC_BatchSource.currentCode,SdkC_BatchSource.stageCode,
    SdkC_BatchSource.code,values Port4B_Install.leaves (SdkC_Source.dictionary left) (SdkC_Source.dictionary right)]

#print axioms values
#print axioms current
#print axioms stage
end AspisR1.SdkD_BatchFixed
end
