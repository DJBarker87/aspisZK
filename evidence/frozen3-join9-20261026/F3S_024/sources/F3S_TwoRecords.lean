import F3S_FirstRecords
import F3S_SecondRecords
set_option autoImplicit false
namespace AspisR1.F3S_TwoRecords
open Aeneas Aeneas.Std Result S2W_Trace

variable {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)

theorem accepted (sdk : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : AdapterRw.r1_pool_adapter.owned.stage1_owned sdk id accounts1 data1 = ok (.Ok saved))
    (accepted2 : AdapterRw.r1_pool_adapter.owned.stage2_owned sdk id accounts2 data2 slot = ok (.Ok ())) :
    ∃ log semantic pub1 proof1 split pub2 proof2 checkpoint,
      run sdk (S2W_Observation.two sdk id accounts1 data1 accounts2 data2 slot) [] = ok (.Ok saved,log) ∧
      F3S_Segments.all adapter ops stage finish reserved query geo B std hashv log =
        [(.first semantic pub1 proof1 split (.Ok saved),
          RawK_TraceLogs.eventLog hashv (GExq_Caller.child adapter ops stage finish reserved query geo B std hashv)
            (.returned (.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 sdk)
              semantic pub1 proof1 split () none) (.Ok saved))),
         (.second pub2 proof2 checkpoint (.Ok ()),
          RawK_TraceLogs.eventLog hashv (GExq_Caller.child adapter ops stage finish reserved query geo B std hashv)
            (.returned (.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 sdk)
              pub2 proof2 checkpoint () none) (.Ok ())))] := by
  obtain ⟨firstLog,first⟩ := S2W_TraceFacts.success_exists sdk
    (S2W_Outer.stage1_owned sdk S2W_Outer.traceEffects id accounts1 data1) [] (.Ok saved)
    ((S2W_OuterErasure.stage1_erasure sdk id accounts1 data1).trans accepted1)
  obtain ⟨secondLog,second⟩ := S2W_TraceFacts.success_exists sdk
    (S2W_Outer.stage2_owned sdk S2W_Outer.traceEffects id accounts2 data2 slot) [] (.Ok ())
    ((S2W_OuterErasure.stage2_erasure sdk id accounts2 data2 slot).trans accepted2)
  have shifted := S2W_TraceSplice.run_shift sdk
    (S2W_Outer.stage2_owned sdk S2W_Outer.traceEffects id accounts2 data2 slot) firstLog []
  simp only [List.append_nil,second,thenResult] at shifted
  obtain ⟨semantic,pub1,proof1,split,firstShape⟩ := F3S_FirstRecords.first_records adapter ops stage finish reserved query geo B std hashv sdk id accounts1 data1 saved firstLog first
  obtain ⟨pub2,proof2,checkpoint,secondShape⟩ := F3S_SecondRecords.second_records adapter ops stage finish reserved query geo B std hashv sdk id accounts2 data2 slot secondLog second
  refine ⟨firstLog++secondLog,semantic,pub1,proof1,split,pub2,proof2,checkpoint,?_,?_⟩
  · simp only [S2W_Observation.two,S2W_TraceFacts.run_bind,first,shifted,thenResult]
    rfl
  · simp only [F3S_Segments.all,List.flatMap_append]
    change F3S_Segments.all adapter ops stage finish reserved query geo B std hashv firstLog ++
      F3S_Segments.all adapter ops stage finish reserved query geo B std hashv secondLog = _
    rw [firstShape,secondShape]
    rfl

#print axioms accepted
end AspisR1.F3S_TwoRecords
