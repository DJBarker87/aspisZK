import PFin_WorldSchedule
import F3V_Checkpoint
import PFin_WorldSource
import F3U_ReifyExact
import F3V_FirstCode
import F3V_SecondComplete
import GExp_SecondSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_WorldPrefix
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem prefix {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : Submission)
    (H : Bytes → State) (e : Evidence c B s H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (accepted : (eval H (F3T_Installed.source c hashv (input c s))).2=true)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std)
      (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize () none=ok (.Ok e.saved))
    (prior : Program Bytes State Unit) :
    ∃ suffix, (eval H prior).1 ++ (eval H (F3T_Installed.source c hashv (input c s))).1=
      F3V_Checkpoint.trace c B s H e prior ++ suffix := by
  obtain ⟨p,a,root,view,read,range,copy,batch,schedule⟩ := PFin_WorldSchedule.log c B s H e hashv accepted first
  have lower := AuS1_Observe.lower (F3U_Oracle.hashv H)
    (SdkD_PrepareSource.code (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
      c.boundaries c.std (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.proof ()
        (Array.repeat 29#usize e.run.zero))
    (AuS1_Prepare.uniform _ _ _ _ (F3U_Oracle.hashv H) (fun _ _=>rfl) _ _ _ _) []
  simp only [SdkC_Source.readLog,List.filterMap_nil,List.nil_append] at lower
  rw [lower] at schedule
  refine ⟨_,?_⟩
  rw [schedule]
  simp only [F3V_Checkpoint.trace,AuS1_Recovery.log,List.append_assoc]

#print axioms prefix
end AspisR1.PFin_WorldPrefix
end
