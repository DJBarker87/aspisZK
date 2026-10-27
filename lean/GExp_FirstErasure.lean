import GExp_FirstCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_FirstErasure
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open CheckpointBytes5Effect
open GExp_FirstCode
local instance : MonadLift Result Code where monadLift := liftResult

theorem erase_liftM {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (r : Result A) : erase (SdkC_Source.dictionary hashv) () (monadLift r : Code A) = r :=
  erase_lift _ _ r

theorem prepare (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Unit) (law : ∀ parts, D.digest () parts = hashv parts)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    erase (SdkC_Source.dictionary hashv) ()
      (SdkD_PrepareLower.lower (SdkD_PrepareSource.code
        (Op5T_Concrete.current {base with op16 := Tx1Q_Install.writer}) B std D pub proof () g)) =
    verifier.candidate.prepare (installed base B std) D pub proof () none g := by
  have association : SdkD_PrepareLower.Associated hashv
      (SdkD_PrepareSource.code
        (Op5T_Concrete.current {base with op16 := Tx1Q_Install.writer}) B std D pub proof () g) :=
    GExp_PrepareAssociation.prepare _ _ _ D pub proof () g hashv (fun _ => law)
  exact (SdkD_PrepareLower.erasure hashv _ association).trans
    (SdkD_PrepareSource.source _ _ _ _ _ _ _ _)

theorem batch (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Unit) (law : ∀ parts, D.digest () parts = hashv parts)
    (proof : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize) :
    erase (SdkC_Source.dictionary hashv) () (SdkC_BatchSource.currentCode hashv proof p root) =
    Op5T_Install.currentBatch Port4B_Install.leaves D proof p root 0#usize () := by
  rw [← SdkC_Source.erasure hashv _ []]
  exact SdkC_BatchSource.current_source hashv D law proof p root []

theorem writer (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Unit) (law : ∀ parts, D.digest () parts = hashv parts)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) :
    erase (SdkC_Source.dictionary hashv) () (writerCode p a proof pub) =
    Tx1Q_Install.writer D p a proof pub () := by
  simp only [writerCode,erase_bind,erase_pure]
  unfold Tx1Q_Install.writer Port3_CheckpointInstall.writer
  congr 1
  unfold CheckpointBytes5Writer.writer
  simp only [erase_bind,erase_read,erase_pure,SdkC_Source.dictionary]
  simp only [VTop_Checkpoint.digest,Tx1Q_Install.digest,law]

#print axioms erase_liftM
#print axioms prepare
#print axioms batch
#print axioms writer
end AspisR1.GExp_FirstErasure
end
