import RPz8_F3U_LoweredHead
import RPz8_F3S_FirstHeader
import RawK_ModelHead
/-! PIN2 W9 (2026-11-11): STATEMENT CHANGE in the serializer conjunct only, propagated from
F3U_SemanticHead.first: the frozen `public_bytes X = ok (.Ok encoded)` becomes the PIN2 emission's
`public_bytes (PreparationBinding.toPIN2 X) = ok (.Ok encoded)` (the serializer the PIN2 verifier
runs; W7 `PublicInitCall.serialized`).  The head conjunct and the proof text are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_FirstHead
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem first {Hash : Type} (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Hash)
    (law : ∀ h parts,D.digest h parts=hashv parts)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (hash : Hash) (saved : alloc.vec.Vec U8)
    (success : erase (SdkC_Source.dictionary hashv) ()
      (GExq_FirstCode.code base B std hashv D pub publicBytes proof split hash)=ok (.Ok saved)) :
    ∃ (encoded : alloc.vec.Vec U8) (root state : State),
      AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (AspisR1PublicPreparation.PreparationBinding.toPIN2 (FirstComposition.toRetainedPublic pub))=ok (.Ok encoded) ∧
      RawK_CodeHead.head hashv (GExq_FirstCode.code base B std hashv D pub publicBytes proof split hash)=
        some (AspisR1.PublicInitFrame.frame (AspisR1PublicPreparation.SourceDigestAddresses.rawBytes encoded.deref) root,state) := by
  obtain ⟨zero,p,scratch,hzero,prepared,tail,logs⟩ :=
    F3S_FirstHeader.split base B std hashv D pub publicBytes proof split hash saved success
  obtain ⟨encoded,root,state,serialized,head⟩ := F3U_LoweredHead.first
    (Op5T_Concrete.current {base with op16:=Tx1Q_Install.writer}) B std hashv D law
    pub proof hash p (Array.repeat 29#usize zero) scratch prepared
  refine ⟨encoded,root,state,serialized,?_⟩
  unfold RawK_CodeHead.head at head ⊢
  rw [logs]
  exact RawK_ModelHead.append_head _ _ _ head

#print axioms first
end AspisR1.F3U_FirstHead
end
