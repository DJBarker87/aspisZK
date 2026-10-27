import GExq_FirstRecords
import GExq_SecondRecords
set_option autoImplicit false
namespace AspisR1.GExq_TwoRecords
open Aeneas Aeneas.Std Result S2W_Trace

theorem accepted (sdk : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : AdapterRw.r1_pool_adapter.owned.stage1_owned sdk id accounts1 data1 = ok (.Ok saved))
    (accepted2 : AdapterRw.r1_pool_adapter.owned.stage2_owned sdk id accounts2 data2 slot = ok (.Ok ())) :
    ∃ log semantic pub1 proof1 split pub2 proof2 checkpoint,
      run sdk (S2W_Observation.two sdk id accounts1 data1 accounts2 data2 slot) [] = ok (.Ok saved,log) ∧
      GExq_RecordTrace.projectLog log =
        [.first semantic pub1 proof1 split (.Ok saved),.second pub2 proof2 checkpoint (.Ok ())] := by
  obtain ⟨firstLog,first⟩ := S2W_TraceFacts.success_exists sdk
    (S2W_Outer.stage1_owned sdk S2W_Outer.traceEffects id accounts1 data1) [] (.Ok saved)
    ((S2W_OuterErasure.stage1_erasure sdk id accounts1 data1).trans accepted1)
  obtain ⟨secondLog,second⟩ := S2W_TraceFacts.success_exists sdk
    (S2W_Outer.stage2_owned sdk S2W_Outer.traceEffects id accounts2 data2 slot) [] (.Ok ())
    ((S2W_OuterErasure.stage2_erasure sdk id accounts2 data2 slot).trans accepted2)
  have shifted := S2W_TraceSplice.run_shift sdk
    (S2W_Outer.stage2_owned sdk S2W_Outer.traceEffects id accounts2 data2 slot) firstLog []
  simp only [List.append_nil,second,thenResult] at shifted
  obtain ⟨semantic,pub1,proof1,split,firstShape⟩ := GExq_FirstRecords.first_records sdk id accounts1 data1 saved firstLog first
  obtain ⟨pub2,proof2,checkpoint,secondShape⟩ := GExq_SecondRecords.second_records sdk id accounts2 data2 slot secondLog second
  refine ⟨firstLog++secondLog,semantic,pub1,proof1,split,pub2,proof2,checkpoint,?_,?_⟩
  · simp only [S2W_Observation.two,S2W_TraceFacts.run_bind,first,shifted,thenResult]
    rfl
  · rw [GExq_RecordTrace.project_append,firstShape,secondShape]
    rfl

#print axioms accepted
end AspisR1.GExq_TwoRecords
