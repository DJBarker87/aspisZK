import RawJ_VerifyBegin
import RawJ_RecordPayload
import S1SemanticInstallationV1
import S1SemanticCurrentCodeV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_SemanticC2
open Aeneas Aeneas.Std Result FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation.PreparedHashCode AuS1_Suffix
open AspisR1CurrentCaller
attribute [local irreducible] S1SemanticCodeInstallation.code

theorem frame (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (input : Slice U8) (hash : H)
    (out : r1_semantic.Verified H)
    (success : erase (S1SemanticCodeInstallation.code R B D pub input hash) = ok (.Ok out)) :
    ∃ (root0 root1 : Array U8 32#usize), out.roots = Array.make 2#usize [root0,root1] ∧
      ∃ frame, Read (observe (run (S1SemanticCodeInstallation.code R B D pub input hash)).1) frame ∧
        BinRawByteCollisionTargets.pred 2 frame = some (decodeState root1) := by
  have native := (S1SemanticCodeInstallation.source R B D pub input hash).symm.trans success
  obtain ⟨pre,initial,after,challenges,payload,root2,parsed,_,_,_,payloadCall,copy,bytes,roots⟩ :=
    S1SemanticInstallation.verify_roots R B D pub input hash out native
  let code := S1SemanticCodeInstallation.code R B D pub input hash
  have inc : ∀ frame, Read (observe (run code).1) frame → Read (observe (run code).1) frame := fun _ h => h
  change ∃ root0 root1, _ ∧ ∃ frame, Read (observe (run code).1) frame ∧ _
  unfold code S1SemanticCodeInstallation.code at success inc
  obtain ⟨result,call,tail,logs⟩ := AuS1_Trace.success_bind _ _ _ success
  cases result with
  | Err e => rw [erase_pure] at tail; cases tail
  | Ok sem =>
    obtain ⟨actual,before,afterBegin,cs,parsed2,begin,contains⟩ := RawJ_VerifyBegin.reached _ _ _ _ _ _ sem call
    have same : actual = pre := core.result.Result.Ok.inj (Result.ok.inj (parsed2.symm.trans parsed))
    subst actual
    obtain ⟨before2,after2,record,q,valid,ran,inside⟩ := RawJ_BeginC2.reached _ _ _ _ _ begin
    obtain ⟨preBytes,shape⟩ := RawJ_RecordPayload.framed pre 2#u8 record payload root2 valid payloadCall bytes.symm
    obtain ⟨tag,_,read⟩ := RawJ_ValidatedRead.frame _ _ _ record q ran
    refine ⟨pre.c1_root,root2,roots,flatten (RawJ_SampleRead.parts before2.state tag record.framed),?_,?_⟩
    · exact inc _ (left_read _ _ _ success _ (contains _ (inside _ read)))
    · exact RawJ_SampleRead.target before2.state tag record.framed root2 preBytes shape

#print axioms frame
end AspisR1.RawJ_SemanticC2
end
