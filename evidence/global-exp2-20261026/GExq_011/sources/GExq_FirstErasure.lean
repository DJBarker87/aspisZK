import GExq_FirstCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_FirstErasure
open Aeneas Aeneas.Std Result AspisR1CurrentCaller CheckpointBytes5Effect
open GExp_FirstCode (installed writerCode)

theorem prepare {Hash : Type} (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash) (law : ∀ h parts, D.digest h parts = hashv parts)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : Hash) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    erase (SdkC_Source.dictionary hashv) ()
      (SdkD_PrepareLower.lower (SdkD_PrepareSource.code
        (Op5T_Concrete.current {base with op16 := Tx1Q_Install.writer}) B std D pub proof hash g)) =
    verifier.candidate.prepare (installed base B std) D pub proof hash none g := by
  exact (SdkD_PrepareLower.erasure hashv _
    (GExp_PrepareAssociation.prepare _ _ _ D pub proof hash g hashv law)).trans
    (SdkD_PrepareSource.source _ _ _ _ _ _ _ _)

theorem batch {Hash : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (law : ∀ parts, D.digest hash parts = hashv parts)
    (proof : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize) :
    erase (SdkC_Source.dictionary hashv) () (SdkC_BatchSource.currentCode hashv proof p root) =
    Op5T_Install.currentBatch Port4B_Install.leaves D proof p root 0#usize hash := by
  let E : AspisR1Stage2.aspis_core.digest.Digest32 Hash :=
    {coremarkerCopyInst := D.coremarkerCopyInst, digest := D.digest}
  rw [← SdkC_Source.erasure hashv _ [],SdkC_Source.erasure_to E hash hashv law]
  simp only [SdkC_BatchSource.currentCode,SdkC_BatchSource.map_erasure,SdkC_BatchSource.erasure]
  rfl

theorem writer {Hash : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (law : ∀ parts, D.digest hash parts = hashv parts)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) :
    erase (SdkC_Source.dictionary hashv) () (writerCode p a proof pub) =
    Tx1Q_Install.writer D p a proof pub hash := by
  simp only [writerCode,erase_bind,erase_pure]
  unfold Tx1Q_Install.writer Port3_CheckpointInstall.writer
  congr 1
  unfold CheckpointBytes5Writer.writer
  simp only [erase_bind,erase_read,erase_pure,SdkC_Source.dictionary]
  simp only [VTop_Checkpoint.digest,Tx1Q_Install.digest,law]

#print axioms prepare
#print axioms batch
#print axioms writer
end AspisR1.GExq_FirstErasure
end
