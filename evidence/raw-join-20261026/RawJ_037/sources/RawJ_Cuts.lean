import RawJ_FirstTraceFields
import RawJ_SecondTraceFields
import S2W_TraceSplice
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_Cuts
open Aeneas Aeneas.Std Result S2W_NativeConsolidation S2W_Trace
open MultiproofConeCanonical

theorem accepted (sdk : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : AdapterRw.r1_pool_adapter.owned.stage1_owned sdk id accounts1 data1 = ok (.Ok saved))
    (accepted2 : AdapterRw.r1_pool_adapter.owned.stage2_owned sdk id accounts2 data2 slot = ok (.Ok ())) :
    ∃ (f : FirstCut) (s : SecondCut) (log : Log),
      SourceCuts sdk accounts1 accounts2 saved f s ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok f.semantic ∧
      run sdk (S2W_Observation.two sdk id accounts1 data1 accounts2 data2 slot) [] = ok (.Ok saved,log) ∧
      GExq_RecordTrace.projectLog log =
        [.first f.semantic f.pub f.proof f.split (.Ok saved),.second s.pub s.proof s.checkpoint (.Ok ())] := by
  obtain ⟨log1,first⟩ := S2W_TraceFacts.success_exists sdk
    (S2W_Outer.stage1_owned sdk S2W_Outer.traceEffects id accounts1 data1) [] (.Ok saved)
    ((S2W_OuterErasure.stage1_erasure sdk id accounts1 data1).trans accepted1)
  obtain ⟨log2,second⟩ := S2W_TraceFacts.success_exists sdk
    (S2W_Outer.stage2_owned sdk S2W_Outer.traceEffects id accounts2 data2 slot) [] (.Ok ())
    ((S2W_OuterErasure.stage2_erasure sdk id accounts2 data2 slot).trans accepted2)
  obtain ⟨pa,pu,raw,pub,statement,semantic,proof,split,ip,iu,rp,ru,dec,get,range,len,call,shape1⟩ :=
    RawJ_FirstTraceFields.fields sdk id accounts1 data1 saved log1 first
  obtain ⟨pa2,ca2,raw2,checkpoint,encoded,proof2,finish,ip2,ic2,rp2,rc2,range2,len2,call2,shape2⟩ :=
    RawJ_SecondTraceFields.fields sdk id accounts2 data2 slot log2 second
  have suffix1 := AdapterRw.Ranges.suffix_exact raw proof 688#usize 58295#usize
    (by scalar_tac) (by simpa using len) range
  have suffix2 := AdapterRw.Ranges.suffix_exact raw2 proof2 688#usize finish
    (S2X.successful_range_ordered _ _ _ _ range2) len2 range2
  let f : FirstCut := ⟨pa,pu,raw,pub,statement,semantic,proof,split⟩
  let s : SecondCut := ⟨pa2,ca2,raw2,checkpoint,encoded,proof2,finish⟩
  refine ⟨f,s,log1++log2,?_,get,?_,?_⟩
  · refine ⟨ip,iu,rp,ru,dec,call,?_,?_,ip2,ic2,rp2,rc2,range2,len2,call2,?_⟩
    · simpa [f,bytesOf] using suffix1.1
    · simpa [f,bytesOf] using congrArg bytesOf suffix1.2
    · simpa [s,bytesOf] using congrArg bytesOf suffix2.2
  · have shifted := S2W_TraceSplice.run_shift sdk
      (S2W_Outer.stage2_owned sdk S2W_Outer.traceEffects id accounts2 data2 slot) log1 []
    simp only [List.append_nil,second,thenResult] at shifted
    simp only [S2W_Observation.two,S2W_TraceFacts.run_bind,first,shifted,thenResult]
    rfl
  · rw [GExq_RecordTrace.project_append,shape1,shape2]
    rfl

#print axioms accepted
end AspisR1.RawJ_Cuts
end
