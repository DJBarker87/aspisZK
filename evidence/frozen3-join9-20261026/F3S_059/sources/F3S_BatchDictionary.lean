import F3S_BatchTree
import GExq_BatchSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_BatchDictionary
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect
 theorem values (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D E : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize) (roots : Array (Array U8 32#usize) 3#usize) (which : Usize) :
    Port9OR_Batch.values base D hash proof queries roots which=
      Port9OR_Batch.values base E hash proof queries roots which := by
  unfold Port9OR_Batch.values
  simp only [F3S_BatchTree.dictionary base D E]
 theorem code {Hash : Type} (D E : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (queries : Array U32 22#usize)
    (roots : Array (Array U8 32#usize) 2#usize) (folded : Array U8 32#usize) (which : Usize) :
    SdkC_BatchSource.code D hash proof queries roots folded which=
      SdkC_BatchSource.code E hash proof queries roots folded which := by
  unfold SdkC_BatchSource.code
  simp only [values Port4B_Install.leaves D E]
 theorem current (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Array U8 32#usize) :
    GExq_BatchSource.current D () proof p root=SdkC_BatchSource.currentCode hashv proof p root := by
  unfold GExq_BatchSource.current SdkC_BatchSource.currentCode
  rw [code _ (SdkC_Source.dictionary hashv)]
 theorem stage (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize) :
    GExq_BatchSource.stage D () proof p root=SdkC_BatchSource.stageCode hashv proof p root := by
  unfold GExq_BatchSource.stage SdkC_BatchSource.stageCode
  rw [code _ (SdkC_Source.dictionary hashv)]
#print axioms values
#print axioms code
#print axioms current
#print axioms stage
end AspisR1.F3S_BatchDictionary
end
