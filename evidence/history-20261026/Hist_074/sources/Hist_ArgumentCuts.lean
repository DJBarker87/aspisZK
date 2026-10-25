import S2W_NativeConsolidation
import AdapterRwAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_ArgumentCuts
open Aeneas Aeneas.Std Result S2W_NativeConsolidation
open MultiproofConeCanonical AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Strengthened acceptance factory retains the semantic getter and actual
TX2 validation/encoder result that the older SourceCuts record projects away.
These are actual successful source calls, not a second selected execution. -/
theorem source (ops : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (firstAccepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts1 data1 = ok (.Ok saved))
    (secondAccepted : AdapterRw.r1_pool_adapter.owned.stage2_owned ops program accounts2 data2 slot = ok (.Ok ())) :
    ∃ f s validated,
      SourceCuts ops accounts1 accounts2 saved f s ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok f.semantic ∧
      AdapterRw.r1_pool_adapter.owned.validate_asq8 ops program accounts2 data2 slot = ok (.Ok validated) ∧
      ops.op22 validated.statement = ok (.Ok s.encoded) := by
  obtain ⟨pa,pu,pub,raw,statement,semantic,proof,split,ipa,ipu,rpa,rpu,decoder,getter,range,first,length⟩ :=
    AdapterRw.Accepted.first_call ops program accounts1 data1 saved firstAccepted
  have shape := AdapterRw.Ranges.suffix_exact raw proof 688#usize 58295#usize
    (by scalar_tac) (by simpa using length) range
  obtain ⟨validated,pa2,ca2,raw2,cp2,encoded,proof2,finish,validation,ipa2,ica2,rpa2,rca2,encoder,range2,second,length2⟩ :=
    S2X.second_fixed_range ops program accounts2 data2 slot secondAccepted
  have shape2 := (AdapterRw.Ranges.suffix_exact raw2 proof2 688#usize finish
    (S2X.successful_range_ordered raw2 proof2 688#usize finish range2) length2 range2).2
  let f : FirstCut := ⟨pa,pu,raw,pub,statement,semantic,proof,split⟩
  let s : SecondCut := ⟨pa2,ca2,raw2,cp2,encoded,proof2,finish⟩
  refine ⟨f,s,validated,?_,getter,validation,encoder⟩
  refine ⟨ipa,ipu,rpa,rpu,decoder,first,?_,?_,ipa2,ica2,rpa2,rca2,range2,length2,second,?_⟩
  · simpa [f,bytesOf] using shape.1
  · have suffix := shape.2
    change raw.val = raw.val.take 688 ++ proof.val at suffix
    simpa only [f,bytesOf,List.map_append,List.map_take] using congrArg bytesOf suffix
  · change raw2.val = raw2.val.take 688 ++ proof2.val at shape2
    simpa only [s,bytesOf,List.map_append,List.map_take] using congrArg bytesOf shape2

#print axioms source
end AspisR1.Hist_ArgumentCuts
end
