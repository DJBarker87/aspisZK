import RPz7_F3W_Runs
import F3U_ReifyExact
import RPz7_F3U_ReifyFirst
import RPz7_F3V_SecondComplete
import RPz7_F3U_SourceInputs
import RPz7_F3U_Slice
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3W_SourceLog
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem evaluated {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
        c.boundaries c.std) (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
        e.pub e.proof 10#usize () none=ok (.Ok e.saved)) :
    eval H (F3T_Installed.source c hashv (input c s))=
      (SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
        (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
          c.boundaries c.std hashv (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
          e.pub e.proof 10#usize) []).2 ++
       SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
        (GExp_SecondCode.code (stage c) c.reserved hashv (digest c)
          e.pub e.proof e.saved.deref) []).2,true) := by
  have one := F3U_ReifyExact.exact
    (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
      c.boundaries c.std hashv (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
      e.pub e.proof 10#usize) H
  have two := F3U_ReifyExact.exact
    (GExp_SecondCode.code (stage c) c.reserved hashv (digest c) e.pub e.proof e.saved.deref) H
  have oneValue : (SdkC_Source.run (F3U_Oracle.hashv H)
    (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
      c.boundaries c.std hashv (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
      e.pub e.proof 10#usize) []).1=ok (.Ok e.saved) := by
    rw [SdkC_Source.erasure, F3V_FirstCode.same H]
    rw [GExp_FirstSource.source _ c.boundaries c.std (F3U_Oracle.hashv H) (D1 c H) (fun _=>rfl)]
    exact first
  have twoValue : (SdkC_Source.run (F3U_Oracle.hashv H)
    (GExp_SecondCode.code (stage c) c.reserved hashv (digest c) e.pub e.proof e.saved.deref) []).1=ok (.Ok ()) := by
    rw [SdkC_Source.erasure,F3V_SecondComplete.same H]
    rw [GExp_SecondSource.source (stage c) c.reserved (F3U_Oracle.hashv H) (D2 c H) (fun _=>rfl)]
    exact e.second
  rw [oneValue] at one
  rw [twoValue] at two
  have pub : Port1_Driver.asSlice s.publicBytes=some e.pub := by
    rw [←e.pubBytes];exact F3U_Slice.roundtrip _
  have proof : Port1_Driver.asSlice s.stored=some e.proof := by
    rw [←e.proofBytes];exact F3U_Slice.roundtrip _
  simp only [F3T_Installed.source,input,pub,proof,e.decoded]
  simp only [DrvC_PairProgram.source,GExp_Experiment.first,GExp_Experiment.second,eval_bind,
    one,two,Port1_Driver.verdict,eval,List.append_nil]

#print axioms evaluated
end AspisR1.F3W_SourceLog
end
