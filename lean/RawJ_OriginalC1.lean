import GExq_CallerRecord

import RawJ_ChildC1
import GExq_FirstEvent
import GExq_EventGood
import GExq_RecordLog
import GExq_OuterGoodTwo
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_OriginalC1
open Aeneas Aeneas.Std Result GExq_OuterLower FS2.Duplex

theorem frame {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : S2Z.Oracle.NativeBinding (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) hashv)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (log : S2W_Trace.Log)
    (ran : S2W_Trace.run (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
      (S2W_Observation.two (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
        id accounts1 data1 accounts2 data2 slot) [] = ok (.Ok saved,log))
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize)
    (member : GExq_OuterRecord.Event.first semantic pub proof split (.Ok saved) ∈ GExq_RecordTrace.projectLog log)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire = MultiproofConeCanonical.bytesOf proof.val) :
    ∃ frame, Read (SdkC_Source.readLog (SdkC_Source.run hashv
      (GExq_CallerRecord.code adapter ops stage finish reserved query geo B std hashv
        id accounts1 accounts2 data1 data2 slot) []).2) frame ∧
      BinRawByteCollisionTargets.pred 2 frame = some (OraclePortBatchDraft.committedRoot parsed 0) := by
  let sdk := GExq_Caller.sdk adapter ops stage finish reserved query geo B std
  let code := S2W_Observation.two sdk id accounts1 data1 accounts2 data2 slot
  have good := GExq_OuterGoodTwo.two sdk hashv law id accounts1 accounts2 data1 data2 slot
  obtain ⟨Hash,D,hash,obs,belongs⟩ := GExq_FirstEvent.occurrence log semantic pub proof split saved member
  have admissible := GExq_EventGood.on_run sdk hashv code good [] log (.Ok saved) (by simp) ran _ belongs
  obtain ⟨digest,obsEq⟩ := admissible
  subst obs
  have called := S2W_TraceFacts.run_valid sdk code [] log (.Ok saved) (by simp) ran _ belongs
  obtain ⟨frame,read,target⟩ := RawJ_ChildC1.frame adapter ops stage finish reserved query geo B std
    hashv D semantic pub proof split hash saved digest called parsed wire
  have contains := GExq_ContainingRead.from_empty sdk hashv
    (GExq_Caller.child adapter ops stage finish reserved query geo B std hashv)
    (GExq_ChildCode.erasure adapter ops stage finish reserved query geo B std hashv)
    code good log (.Ok saved) ran _ belongs
  refine ⟨frame,?_,target⟩
  change Read (SdkC_Source.readLog (SdkC_Source.run hashv
    (GExq_OuterRecord.record (GExq_Caller.child adapter ops stage finish reserved query geo B std hashv) code []) []).2) frame
  rw [GExq_RecordLog.log]
  exact contains frame read

#print axioms frame
end AspisR1.RawJ_OriginalC1
end
