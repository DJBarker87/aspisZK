import PFin_WorldSource
import F3U_ReifyExact
import F3V_FirstCode
import F3V_SecondComplete
import GExp_SecondSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_WorldEval
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem log {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : Submission)
    (H : Bytes → State) (e : Evidence c B s H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (accepted : (eval H (F3T_Installed.source c hashv (input c s))).2=true)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std)
      (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize () none=ok (.Ok e.saved)) :
    eval H (F3T_Installed.source c hashv (input c s))=
      (SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
        (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
          c.boundaries c.std hashv (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
          e.pub e.proof 10#usize) []).2 ++
       SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
        (GExp_SecondCode.code (stage c) c.reserved hashv (digest c) e.pub e.proof e.saved.deref) []).2,true) := by
  let code1 := GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
    c.boundaries c.std hashv (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize
  let code2 := GExp_SecondCode.code (stage c) c.reserved hashv (digest c) e.pub e.proof e.saved.deref
  have firstErased : erase (SdkC_Source.dictionary (F3U_Oracle.hashv H)) () code1=ok (.Ok e.saved) := by
    dsimp only [code1]
    rw [F3V_FirstCode.same H _ _ _ hashv (currentDigest c)]
    rw [GExp_FirstSource.source _ _ _ (F3U_Oracle.hashv H) (D1 c H) (fun _=>rfl)]
    exact first
  have secondErased : erase (SdkC_Source.dictionary (F3U_Oracle.hashv H)) () code2=ok (.Ok ()) := by
    dsimp only [code2]
    rw [F3V_SecondComplete.same H _ _ hashv (digest c)]
    rw [GExp_SecondSource.source _ _ (F3U_Oracle.hashv H) (D2 c H) (fun _=>rfl)]
    exact e.second
  have one := F3U_ReifyExact.exact code1 H
  have two := F3U_ReifyExact.exact code2 H
  have oneValue := (SdkC_Source.erasure (F3U_Oracle.hashv H) code1 []).trans firstErased
  have twoValue := (SdkC_Source.erasure (F3U_Oracle.hashv H) code2 []).trans secondErased
  rw [oneValue] at one
  rw [twoValue] at two
  rw [PFin_WorldSource.program c B s H e hashv accepted]
  dsimp only [code1] at one
  dsimp only [code2] at two
  simp only [DrvC_PairProgram.source,GExp_Experiment.first,GExp_Experiment.second,eval_bind,
    one,two,Port1_Driver.verdict,eval,List.append_nil]

#print axioms log
end AspisR1.PFin_WorldEval
end
