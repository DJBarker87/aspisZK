import RPz7_GExq_FirstFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_FirstRoot
open Aeneas Aeneas.Std Result AspisR1CurrentCaller CheckpointBytes5Effect FS2.Duplex

theorem frame {Hash : Type} (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash) (law : ∀ h parts, D.digest h parts = hashv parts)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (hash : Hash) (saved : alloc.vec.Vec U8)
    (success : erase (SdkC_Source.dictionary hashv) ()
      (GExq_FirstCode.code base B std hashv D pub publicBytes proof split hash) = ok (.Ok saved))
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire = MultiproofConeCanonical.bytesOf proof.val) :
    ∃ frame, Read (SdkC_Source.readLog (SdkC_Source.run hashv
      (GExq_FirstCode.code base B std hashv D pub publicBytes proof split hash) []).2) frame ∧
      BinRawByteCollisionTargets.pred 3 frame = some (OraclePortBatchDraft.committedRoot parsed 2) := by
  obtain ⟨input,scratch,p,prepare,contains⟩ :=
    GExq_FirstFrame.reached base B std hashv D pub publicBytes proof split hash saved success
  have source := GExq_FirstErasure.prepare base B std hashv D law pub proof hash input
  have accepted := source.symm.trans prepare
  obtain ⟨frame,read,target⟩ := GExq_PrepareFrame.frame
    (Op5T_Concrete.current {base with op16 := Tx1Q_Install.writer}) B std hashv D law
    pub proof hash p input scratch accepted parsed wire
  exact ⟨frame,contains frame read,target⟩

#print axioms frame
end AspisR1.GExq_FirstRoot
end
