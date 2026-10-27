import RPz7_GExq_BatchSource
import RPz8_SCG_BatchDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_BatchCode
open Aeneas Aeneas.Std Result

/-- Test the literal code carrier rather than inferring logs from erasure. -/
theorem current {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared)
    (root : Array U8 32#usize) :
    GExq_BatchSource.current D hash proof p root =
      SdkC_BatchSource.currentCode hashv proof p root := by
  unfold GExq_BatchSource.current SdkC_BatchSource.currentCode
  dsimp only
  rw [SCG_BatchDictionary.code _ (SdkC_Source.dictionary hashv) hash ()]

theorem stage {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared)
    (root : Array U8 32#usize) :
    GExq_BatchSource.stage D hash proof p root =
      SdkC_BatchSource.stageCode hashv proof p root := by
  unfold GExq_BatchSource.stage SdkC_BatchSource.stageCode
  dsimp only
  rw [SCG_BatchDictionary.code _ (SdkC_Source.dictionary hashv) hash ()]

#print axioms current
#print axioms stage
end AspisR1.SCG_BatchCode
end
