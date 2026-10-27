import F3S_TwoRecords
import F3S_TwoSegments
import RawK_RecordedHead
import RawJ_RecordCuts
import GExq_OuterGoodTwo
import GExq_CallerRecord
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_ExactChildren
open Aeneas Aeneas.Std Result GExq_OuterLower

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

theorem exact_children (law : S2Z.Oracle.NativeBinding
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) hashv)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : AdapterRw.r1_pool_adapter.owned.stage1_owned
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) id accounts1 data1=ok (.Ok saved))
    (accepted2 : AdapterRw.r1_pool_adapter.owned.stage2_owned
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std) id accounts2 data2 slot=ok (.Ok ()))
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut) (log : S2W_Trace.Log)
    (ran : S2W_Trace.run (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
      (S2W_Observation.two (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
        id accounts1 data1 accounts2 data2 slot) [] = ok (.Ok saved,log))
    (recorded : RawJ_RecordCuts.Recorded f s saved log) :
    let sdk := GExq_Caller.sdk adapter ops stage finish reserved query geo B std
    let impl := GExq_Caller.child adapter ops stage finish reserved query geo B std hashv
    F3S_Segments.all adapter ops stage finish reserved query geo B std hashv log=
      [(.first f.semantic f.pub f.proof f.split (.Ok saved),
        RawK_TraceLogs.eventLog hashv impl
          (.returned (.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 sdk)
            f.semantic f.pub f.proof f.split () none) (.Ok saved))),
       (.second s.pub s.proof s.checkpoint (.Ok ()),
        RawK_TraceLogs.eventLog hashv impl
          (.returned (.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 sdk)
            s.pub s.proof s.checkpoint () none) (.Ok ())))] := by
  obtain ⟨other,semantic,pub1,proof1,k,pub2,proof2,ck,otherRun,shape⟩ :=
    F3S_TwoRecords.accepted adapter ops stage finish reserved query geo B std hashv
      (GExq_Caller.sdk adapter ops stage finish reserved query geo B std)
      id accounts1 accounts2 data1 data2 slot saved accepted1 accepted2
  have same : other=log := congrArg Prod.snd (Result.ok.inj (otherRun.symm.trans ran))
  subst other
  have projected := F3S_Segments.projection adapter ops stage finish reserved query geo B std hashv log
  rw [shape,recorded.2] at projected
  simp only [List.map_cons,List.map_nil,List.cons.injEq,GExq_OuterRecord.Event.first.injEq,
    GExq_OuterRecord.Event.second.injEq] at projected
  rcases projected with ⟨⟨rfl,rfl,rfl,rfl,_⟩,⟨⟨rfl,rfl,rfl,_⟩,_⟩⟩
  exact shape
#print axioms exact_children
end AspisR1.F3S_ExactChildren
end
