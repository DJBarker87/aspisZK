import SdkC_BatchSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_BatchSource
open Aeneas Aeneas.Std Result CheckpointBytes5Effect

def current {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared)
    (root : Array U8 32#usize) :=
  let E : AspisR1Stage2.aspis_core.digest.Digest32 Hash :=
    {coremarkerCopyInst := D.coremarkerCopyInst, digest := D.digest}
  SdkC_BatchSource.mapCode Op5T_Install.currentError
    (SdkC_BatchSource.code E hash proof p.queries p.roots root 0#usize)

def stage {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (proof : Slice U8) (p : VTop_Stages.verifier.Prepared)
    (root : Array U8 32#usize) :=
  let E : AspisR1Stage2.aspis_core.digest.Digest32 Hash :=
    {coremarkerCopyInst := D.coremarkerCopyInst, digest := D.digest}
  SdkC_BatchSource.mapCode Op5T_Install.stageError
    (SdkC_BatchSource.code E hash proof p.queries p.roots root 1#usize)

theorem current_source {Hash : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (law : ∀ parts, D.digest hash parts = hashv parts)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Array U8 32#usize) :
    erase (SdkC_Source.dictionary hashv) () (current D hash proof p root) =
      Op5T_Install.currentBatch Port4B_Install.leaves D proof p root 0#usize hash := by
  let E : AspisR1Stage2.aspis_core.digest.Digest32 Hash :=
    {coremarkerCopyInst := D.coremarkerCopyInst, digest := D.digest}
  rw [← SdkC_Source.erasure hashv _ [],SdkC_Source.erasure_to E hash hashv law]
  simp only [current,SdkC_BatchSource.map_erasure,SdkC_BatchSource.erasure]
  rfl

theorem stage_source {Hash : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (law : ∀ parts, D.digest hash parts = hashv parts)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize) :
    erase (SdkC_Source.dictionary hashv) () (stage D hash proof p root) =
      Op5T_Install.stageBatch Port4B_Install.leaves D proof p root 1#usize hash := by
  let E : AspisR1Stage2.aspis_core.digest.Digest32 Hash :=
    {coremarkerCopyInst := D.coremarkerCopyInst, digest := D.digest}
  rw [← SdkC_Source.erasure hashv _ [],SdkC_Source.erasure_to E hash hashv law]
  simp only [stage,SdkC_BatchSource.map_erasure,SdkC_BatchSource.erasure]
  rfl

#print axioms current_source
#print axioms stage_source
end AspisR1.GExq_BatchSource
end
