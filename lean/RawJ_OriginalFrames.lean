import GExq_OriginalRoot
import RawJ_OriginalC1
import RawJ_OriginalC2
import RawJ_RecordCuts
import GExq_CallerRecord

import GExq_FirstChildRoot
import GExq_FirstEvent
import GExq_EventGood
import GExq_RecordLog
import GExq_OuterGoodTwo
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_OriginalFrames
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
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (recorded : RawJ_RecordCuts.Recorded f s saved log)
    (parsed : OraclePortCompactDraft.Parsed)
    (parser : OraclePortCompactDraft.parse (MultiproofConeCanonical.bytesOf f.proof.val) = some parsed)
    (wire : parsed.wire = MultiproofConeCanonical.bytesOf f.proof.val) :
    ∀ kind : Fin 3, ∃ frame, Read (SdkC_Source.readLog (SdkC_Source.run hashv
      (GExq_CallerRecord.code adapter ops stage finish reserved query geo B std hashv
        id accounts1 accounts2 data1 data2 slot) []).2) frame ∧
      BinRawByteCollisionTargets.pred (if kind.val = 2 then 3 else 2) frame =
        some (OraclePortBatchDraft.committedRoot parsed kind.val) := by
  have member : GExq_OuterRecord.Event.first f.semantic f.pub f.proof f.split (.Ok saved) ∈
      GExq_RecordTrace.projectLog log := by
    rw [recorded.2]
    exact List.mem_cons_self
  intro kind
  fin_cases kind
  · exact RawJ_OriginalC1.frame adapter ops stage finish reserved query geo B std hashv law
      id accounts1 accounts2 data1 data2 slot saved log ran f.semantic f.pub f.proof f.split member parsed wire
  · exact RawJ_OriginalC2.frame adapter ops stage finish reserved query geo B std hashv law
      id accounts1 accounts2 data1 data2 slot saved log ran f.semantic f.pub f.proof f.split member parsed parser wire
  · exact GExq_OriginalRoot.frame adapter ops stage finish reserved query geo B std hashv law
      id accounts1 accounts2 data1 data2 slot saved log ran f.semantic f.pub f.proof f.split member parsed wire

#print axioms frame
end AspisR1.RawJ_OriginalFrames
end
