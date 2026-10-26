import RPz7_F3V_BatchDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_StageBatch
open Aeneas Aeneas.Std Result

theorem same (first second : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize) :
    SdkC_BatchSource.stageCode first proof p root=SdkC_BatchSource.stageCode second proof p root := by
  simp only [SdkC_BatchSource.stageCode,F3S_BatchDictionary.code
    (SdkC_Source.dictionary first) (SdkC_Source.dictionary second)]

#print axioms same
end AspisR1.F3V_StageBatch
end
