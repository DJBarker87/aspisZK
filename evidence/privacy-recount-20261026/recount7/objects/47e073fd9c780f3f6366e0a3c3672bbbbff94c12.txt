import R1Z.ProverCommitQuery26
import R1Z.ProverCommitArrayIndex25
/-! Totality of the installed concrete query decoder, without a successful
source-call premise. Symbolic induction keeps all input bytes arbitrary. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitQueryTotal26
open Aeneas Aeneas.Std Result
open ProverCommitQuery26
open AspisR1SelectedMaskProbe
open AspisR1QueryScanUnrolled.r0_transcript

theorem from_fn_loop_total {T F : Type} (N : Usize)
    (callback : core.ops.function.FnMut F Usize T)
    (step_total : ∀ f i, i.val < N.val → ∃ value next, callback.call_mut f i = ok (value,next))
    (fuel : Nat) (i : Usize) (f : F) (acc : List T)
    (hi : i.val ≤ N.val) (budget : N.val-i.val < fuel) :
    ∃ values next, arrayFromFnLoop N callback fuel i f acc = ok (values,next) := by
  induction fuel generalizing i f acc with
  | zero => omega
  | succ fuel ih =>
    by_cases more : i < N
    · have hmore : i.val < N.val := more
      obtain ⟨value,next,hcall⟩ := step_total f i hmore
      have cap : N.val ≤ Usize.max := by
        have hb := N.hBounds
        have hm := Usize.max_succ_eq_pow
        change N.val < 2^System.Platform.numBits at hb
        omega
      obtain ⟨j,hj,hjval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      have jval : j.val = i.val+1 := by simpa using hjval
      obtain ⟨values,last,htail⟩ := ih j next (value::acc) (by omega) (by omega)
      refine ⟨values,last,?_⟩
      simp only [arrayFromFnLoop,more,dif_pos,hcall,bind_tc_ok,hj,htail]
    · exact ⟨acc.reverse,f,by simp [arrayFromFnLoop,more]⟩

theorem from_fn_total {T F : Type} (N : Usize)
    (callback : core.ops.function.FnMut F Usize T)
    (step_total : ∀ f i, i.val < N.val → ∃ value next, callback.call_mut f i = ok (value,next))
    (f : F) : ∃ values, AspisR1SelectedMaskProbe.core.array.from_fn N callback f = ok values := by
  obtain ⟨values,last,hrun⟩ := from_fn_loop_total N callback step_total
    (N.val+1) (0#usize) f [] (by scalar_tac) (by scalar_tac)
  unfold AspisR1SelectedMaskProbe.core.array.from_fn
  split
  · exact ⟨_,rfl⟩
  · rename_i error hfail
    rw [hrun] at hfail
    cases hfail
  · rename_i hdiv
    rw [hrun] at hdiv
    cases hdiv

theorem block_rank_total (block : Bytes32) :
    ∃ words, block_rank block = ok words := by
  let cb := block_rank.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
  have steps : ∀ f i, i.val < (8#usize).val → ∃ value next, cb.call_mut f i = ok (value,next) := by
    intro f i hi
    exact ⟨_,f,block_rank_callback_call_mut_success f i hi⟩
  exact from_fn_total (8#usize) cb steps block

theorem map_stable {T U F : Type} (call : F → T → Result (U × F))
    (f : F) (g : T → U) (stable : ∀ x, call f x = ok (g x,f)) (xs : List T) :
    AspisV8R19.TraversalRuntime.mapState call xs f = ok (xs.map g,f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [AspisV8R19.TraversalRuntime.mapState,stable,bind_tc_ok,ih,List.map_cons]

theorem words_total (block : Bytes32) :
    ∃ words, Query31ConcreteWordsDriverChain.actualQueryWords block = ok words := by
  obtain ⟨ranks,hranks⟩ := block_rank_total block
  let cb := query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32
  have hm := map_stable cb.call_mut () queryMaskWord (query_mask_call_mut_exact ()) ranks.val
  have ha := core.array.Array.map_success cb ranks () _ () hm
  refine ⟨⟨ranks.val.map queryMaskWord,by simpa only [List.length_map] using ranks.property⟩,?_⟩
  simp only [Query31ConcreteWordsDriverChain.actualQueryWords,query_words,hranks,bind_tc_ok,
    AspisR1QueryScanUnrolled.core.array.Array.map,AspisR1SelectedMaskProbe.core.array.Array.map]
  exact ha

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
  · refine ⟨core.result.Result.Ok (s.accepted,advances.val[index.val]'(by simpa [advances.property] using hi)),?_⟩
    simp only [finishAdvance,aspis_core.r0_transcript.QueryScan.finish,hc,if_true,
      bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,ha]
  · refine ⟨core.result.Result.Err (aspis_core.transcript.QuerySampleError.DrawLimitExhausted
      s.accepted_len aspis_core.r0_transcript.QUERY_MAX_DRAWS),?_⟩
    simp only [finishAdvance,aspis_core.r0_transcript.QueryScan.finish,hc,if_false,
      bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
    rfl

theorem raw_total (blocks advances : Blocks) : ∃ r, raw blocks advances = ok r := by
  unfold raw queries_from_pairs_with_scan
  have hb0 := ProverCommitArrayIndex25.array_index_usize_ok blocks 0#usize (by decide)
  rw [hb0]
  simp only [bind_tc_ok]
  obtain ⟨stop0,s1,hscan0,valid1⟩ := block_scan_total initial _ initial_valid
  rw [hscan0]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  cases stop0 with
  | true =>
    change ∃ r, finishAdvance advances 0#usize s1 = ok r
    exact finish_total advances 0#usize s1 (by decide)
  | false =>
  have hb1 := ProverCommitArrayIndex25.array_index_usize_ok blocks 1#usize (by decide)
  rw [hb1]
  simp only [bind_tc_ok]
  obtain ⟨stop1,s2,hscan1,valid2⟩ := block_scan_total s1 _ valid1
  rw [hscan1]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  cases stop1 with
  | true =>
    change ∃ r, finishAdvance advances 1#usize s2 = ok r
    exact finish_total advances 1#usize s2 (by decide)
  | false =>
  have hb2 := ProverCommitArrayIndex25.array_index_usize_ok blocks 2#usize (by decide)
  rw [hb2]
  simp only [bind_tc_ok]
  obtain ⟨stop2,s3,hscan2,valid3⟩ := block_scan_total s2 _ valid2
  rw [hscan2]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  cases stop2 with
  | true =>
    change ∃ r, finishAdvance advances 2#usize s3 = ok r
    exact finish_total advances 2#usize s3 (by decide)
  | false =>
  have hb3 := ProverCommitArrayIndex25.array_index_usize_ok blocks 3#usize (by decide)
  rw [hb3]
  simp only [bind_tc_ok]
  obtain ⟨stop3,s4,hscan3,valid4⟩ := block_scan_total s3 _ valid3
  rw [hscan3]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  cases stop3 with
  | true =>
    change ∃ r, finishAdvance advances 3#usize s4 = ok r
    exact finish_total advances 3#usize s4 (by decide)
  | false =>
  have hb4 := ProverCommitArrayIndex25.array_index_usize_ok blocks 4#usize (by decide)
  rw [hb4]
  simp only [bind_tc_ok]
  obtain ⟨stop4,s5,hscan4,valid5⟩ := block_scan_total s4 _ valid4
  rw [hscan4]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  cases stop4 with
  | true =>
    change ∃ r, finishAdvance advances 4#usize s5 = ok r
    exact finish_total advances 4#usize s5 (by decide)
  | false =>
  have hb5 := ProverCommitArrayIndex25.array_index_usize_ok blocks 5#usize (by decide)
  rw [hb5]
  simp only [bind_tc_ok]
  obtain ⟨stop5,s6,hscan5,valid6⟩ := block_scan_total s5 _ valid5
  rw [hscan5]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  cases stop5 with
  | true =>
    change ∃ r, finishAdvance advances 5#usize s6 = ok r
    exact finish_total advances 5#usize s6 (by decide)
  | false =>
  have hb6 := ProverCommitArrayIndex25.array_index_usize_ok blocks 6#usize (by decide)
  rw [hb6]
  simp only [bind_tc_ok]
  obtain ⟨stop6,s7,hscan6,valid7⟩ := block_scan_total s6 _ valid6
  rw [hscan6]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  cases stop6 with
  | true =>
    change ∃ r, finishAdvance advances 6#usize s7 = ok r
    exact finish_total advances 6#usize s7 (by decide)
  | false =>
  have hb7 := ProverCommitArrayIndex25.array_index_usize_ok blocks 7#usize (by decide)
  rw [hb7]
  simp only [bind_tc_ok]
  obtain ⟨stop7,s8,hscan7,valid8⟩ := block_scan_total s7 _ valid7
  rw [hscan7]
  simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
  change ∃ r, finishAdvance advances 7#usize s8 = ok r
  exact finish_total advances 7#usize s8 (by decide)

/-- The installed callback terminates on every pair of block arrays. It may
reject; no source success or arbitrary callback is supplied by the caller. -/
theorem query_total (blocks advances : Blocks) :
    ∃ r, policy.queries blocks advances = ok r := by
  obtain ⟨r,hr⟩ := raw_total blocks advances
  cases r with
  | Ok value => exact ⟨core.result.Result.Ok value,by
      simp only [policy,ProverCommitPolicies25.policy,query,hr,bind_tc_ok]⟩
  | Err error => exact ⟨core.result.Result.Err AspisR1SimControl21.verifier.Error.Transcript,by
      simp only [policy,ProverCommitPolicies25.policy,query,hr,bind_tc_ok]⟩

#print axioms from_fn_loop_total
#print axioms from_fn_total
#print axioms block_rank_total
#print axioms map_stable
#print axioms words_total
#print axioms block_scan_total
#print axioms finish_total
#print axioms raw_total
#print axioms query_total
end R1Z.ProverCommitQueryTotal26
