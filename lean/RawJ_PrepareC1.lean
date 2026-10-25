import RawJ_PrepareSemantic
import S1OriginalNewStaticFieldsV1
import S1SemanticInstallationV1
import SdkD_RootBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_PrepareC1
open Aeneas Aeneas.Std Result FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation.PreparedHashCode
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
attribute [local irreducible] S1PrepareCode.prepare S1SemanticCodeInstallation.code

theorem frame (ops : Ops) (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : erase (S1PrepareCode.prepare ops R B D pub proof hash input) = ok (.Ok p,scratch)) :
    ∃ frame, Read (observe (run (S1PrepareCode.prepare ops R B D pub proof hash input)).1) frame ∧
      BinRawByteCollisionTargets.pred 2 frame =
        some (decodeState (Port3_BatchStage.root0 (Tx1Q_Carriers.prepared p))) := by
  obtain ⟨semantic,y1,view,sem,hview,hsem,hnew,contains⟩ :=
    RawJ_PrepareSemantic.reached ops R B D pub proof hash p input scratch success
  obtain ⟨parsedPrefix,parsed,frame,read,target⟩ := RawJ_SemanticRead.frame R B D pub view.semantic hash sem hsem
  have native := (S1SemanticCodeInstallation.source R B D pub view.semantic hash).symm.trans hsem
  obtain ⟨pre,initial,after,challenges,payload,root2,hparse,_,_,_,_,_,_,roots⟩ :=
    S1SemanticInstallation.verify_roots R B D pub view.semantic hash sem native
  have same : pre = parsedPrefix := core.result.Result.Ok.inj (Result.ok.inj (hparse.symm.trans parsed))
  subst pre
  rw [closedPreparationCode_erasure] at hnew
  have static := originalNew_static _ _ D sem view hash p scratch input hnew
  have root : Port3_BatchStage.root0 (Tx1Q_Carriers.prepared p) = parsedPrefix.c1_root := by
    simp only [Port3_BatchStage.root0,Tx1Q_Carriers.prepared,static.2.1,roots,Array.make]
    rfl
  exact ⟨frame,contains frame read,by rw [root]; exact target⟩

#print axioms frame
end AspisR1.RawJ_PrepareC1
end
