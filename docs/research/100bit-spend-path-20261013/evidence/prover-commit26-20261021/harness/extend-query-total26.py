from pathlib import Path
p=Path('docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitQueryTotal26.lean');s=p.read_text();i=s.index('\n#print axioms from_fn_loop_total')
new='''
open Query31ExplicitListLoop Query31ModelScanCall Query31ConcreteWordsDriverChain
open AspisR1Query31Transcript

theorem block_scan_total (s : Scan) (block : Bytes32) (hs : validState s) :
    ∃ stop sf, modelScanFn actualQueryWords s block = ok (stop,sf) ∧ validState sf := by
  obtain ⟨words,hw⟩ := words_total block
  obtain ⟨sf,pending,hloop,_,hvalid⟩ := scanListLoop_q22_valid words.val s hs
  exact ⟨optionStop pending,sf,by
    simp only [modelScanFn,hw,bind_tc_ok,hloop,Aeneas.Std.uncurry_apply_pair],hvalid⟩

theorem finish_total (advances : Blocks) (index : Usize) (s : Scan) (hi : index.val<8) :
    ∃ r, finishAdvance advances index s = ok r := by
  have ha := ProverCommitArrayIndex25.array_index_usize_ok advances index hi
  by_cases hc : s.accepted_len = aspis_core.r0_transcript.QUERY_COUNT
  · refine ⟨core.result.Result.Ok (s.accepted,_),?_⟩
    simp only [finishAdvance,aspis_core.r0_transcript.QueryScan.finish,hc,if_true,
      bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,ha]
  · refine ⟨core.result.Result.Err (aspis_core.transcript.QuerySampleError.DrawLimitExhausted
      s.accepted_len aspis_core.r0_transcript.QUERY_MAX_DRAWS),?_⟩
    simp only [finishAdvance,aspis_core.r0_transcript.QueryScan.finish,hc,if_false,
      bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]

theorem raw_total (blocks advances : Blocks) : ∃ r, raw blocks advances = ok r := by
  unfold raw queries_from_pairs_with_scan
'''
for i in range(8):
 state='initial' if i==0 else f's{i}'
 valid='initial_valid' if i==0 else f'valid{i}'
 new+=f'''  have hb{i} := ProverCommitArrayIndex25.array_index_usize_ok blocks {i}#usize (by decide)
  rw [hb{i}]
  simp only [bind_tc_ok]
  obtain ⟨stop{i},s{i+1},hscan{i},valid{i+1}⟩ := block_scan_total {state} _ {valid}
  rw [hscan{i}]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
'''
 if i<7:
  new+=f'''  cases stop{i} with
  | true =>
    change ∃ r, finishAdvance advances {i}#usize s{i+1} = ok r
    exact finish_total advances {i}#usize s{i+1} (by decide)
  | false =>
'''
 else:
  new+='''  change ∃ r, finishAdvance advances 7#usize s8 = ok r
  exact finish_total advances 7#usize s8 (by decide)
'''
s=s[:s.index('\n#print axioms from_fn_loop_total')]+new+s[s.index('\n#print axioms from_fn_loop_total'):]
s=s.replace('#print axioms words_total','#print axioms words_total\n#print axioms block_scan_total\n#print axioms finish_total\n#print axioms raw_total');p.write_text(s)
