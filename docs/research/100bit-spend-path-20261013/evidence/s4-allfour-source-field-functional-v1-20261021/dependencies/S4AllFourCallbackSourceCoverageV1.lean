import S4AllFourCallbackHeadTailDecodeV1
import FourDotsActualTermSourceMeaningRootV1
import FourDotsActualTermGeometryRootV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1FastDotsAllFourCallbackSourceCoverageV1

abbrev Ops := AspisR1FastDotsAllFourCallbackHeadTailDecodeV1.Ops
abbrev Wide := AspisR1FastDotsAllFourCallbackHeadTailDecodeV1.Wide
abbrev Contribution := AspisR1FastDotsOuterFoldTraceV2.Contribution
abbrev ExactTrace := AspisR1FastDotsOuterFoldTraceV2.ExactTrace
abbrev SourceMeaning := AspisR1FastDotsActualTermSourceMeaningRootV1.SourceMeaning
abbrev CallbackDecodedTrace :=
  AspisR1FastDotsAllFourCallbackHeadTailDecodeV1.CallbackDecodedTrace

theorem exact_trace_source_meanings
    {ops : Ops} {a : Array Std.U8 608#usize} {g : Array Wide 29#usize}
    {slot : Usize} {it : AspisR1FastDotsOuterFoldTraceV2.StepBy}
    {limbs out : Array Std.U64 8#usize}
    {ds : List (List Contribution)} {starts : List Nat}
    (htrace : ExactTrace ops a g slot it limbs out ds starts) :
    ∀ c ∈ ds.flatten, SourceMeaning a g slot c := by
  induction htrace with
  | stop => simp
  | @step it it' limbs limbs' out cs tail starts hstep4 hnextStep4 hstart
      hcursor hend hbody hbatch htail ih =>
      intro c hc
      have hmem : c ∈ cs ∨ c ∈ tail.flatten := by
        simpa only [List.flatten_cons, List.mem_append] using hc
      rcases hmem with hcs | htailMem
      · exact AspisR1FastDotsActualTermSourceMeaningRootV1.actual_trace_source_meanings
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) a g slot {start := hbatch.start, «end» := hbatch.rangeEnd}
          (Array.repeat 8#usize 0#u64) hbatch.sums cs hbatch.sourceTrace c hcs
      · exact ih c htailMem

/-- Every contribution carried by a successful callback's retained outer
    trace is tied to its actual source bytes, parser result, `g` lookup, and
    limb conversion. -/
theorem callback_trace_source_meanings
    (base ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (value : Wide)
    (h : CallbackDecodedTrace base ops a g slot value) :
    ∃ ds : List (List Contribution), CallbackDecodedTrace base ops a g slot value ∧
      ∀ c ∈ ds.flatten, SourceMeaning a g slot c := by
  rcases h with ⟨ds,starts,limbs,body,tailValue,wide28,q,tailStart,tail2,cs,
    hcb,htrace,hseven,hfirstQuery,hwide28,hrun,hfinish,haccepted,hproduct,
    hfinishWords,hresult⟩
  refine ⟨ds, ?_, ?_⟩
  · exact ⟨ds,starts,limbs,body,tailValue,wide28,q,tailStart,tail2,cs,
      hcb,htrace,hseven,hfirstQuery,hwide28,hrun,hfinish,haccepted,hproduct,
      hfinishWords,hresult⟩
  · exact exact_trace_source_meanings htrace

/-- The term indices in each retained outer batch are exactly the range
    consumed by that batch's actual term-loop trace. -/
theorem exact_trace_batch_term_indices
    {ops : Ops} {a : Array Std.U8 608#usize} {g : Array Wide 29#usize}
    {slot : Usize} {it : AspisR1FastDotsOuterFoldTraceV2.StepBy}
    {limbs out : Array Std.U64 8#usize}
    {ds : List (List Contribution)} {starts : List Nat}
    (htrace : ExactTrace ops a g slot it limbs out ds starts) :
    ∀ cs ∈ ds, ∃ start rangeEnd,
      cs.map (fun c => c.term.val) = List.range' start (rangeEnd - start) := by
  induction htrace with
  | stop => simp
  | @step it it' limbs limbs' out cs tail starts hstep4 hnextStep4 hstart
      hcursor hend hbody hbatch htail ih =>
      intro xs hx
      simp only [List.mem_cons] at hx
      rcases hx with heq | hx
      · subst xs
        refine ⟨hbatch.start.val,hbatch.rangeEnd.val,?_⟩
        simpa using
          AspisR1FastDotsActualTermGeometryRootV1.actual_trace_term_indices
            _ a g slot {start := hbatch.start, «end» := hbatch.rangeEnd}
            (Array.repeat 8#usize 0#u64) hbatch.sums cs hbatch.sourceTrace
      · exact ih xs hx

/-- The flattened successful outer trace visits every term in its source
    interval exactly once and in order. This uses the actual per-batch source
    traces and the actual StepBy cursor transition; no independently supplied
    batch schedule is assumed. -/
theorem exact_trace_flattened_term_indices
    {ops : Ops} {a : Array Std.U8 608#usize} {g : Array Wide 29#usize}
    {slot : Usize} {it : AspisR1FastDotsOuterFoldTraceV2.StepBy}
    {limbs out : Array Std.U64 8#usize}
    {ds : List (List Contribution)} {starts : List Nat}
    (htrace : ExactTrace ops a g slot it limbs out ds starts)
    (hend26 : it.iter.end.val = 26) :
    ds.flatten.map (fun c => c.term.val) = List.range' it.iter.start.val (26 - it.iter.start.val) := by
  revert hend26
  induction htrace with
  | stop it limbs out hstep4 hbody hout =>
      intro hend26
      have hstop := AspisR1FastDotsBatchBodyDone.body_success_done_exhausted
        (AspisR1FastDotsOuterFoldTraceV2.BatchOps
          (AspisR1FastDotsOuterFoldTraceV2.LimbOps ops))
        a g slot it limbs out hstep4 hbody
      have hlen : 26 - it.iter.start.val = 0 := by omega
      simp [hlen]
  | @step it it' limbs limbs' out cs tail starts hstep4 hnextStep4
      hstart hcursor hend hbody hbatch htail ih =>
      intro hend26
      have hstepVal : it.step_by.val = 4 := by rw [hstep4]; scalar_tac
      have hadv := AspisR1FastDotsBatchBodyAdvance.body_success_cont_step
        (AspisR1FastDotsOuterFoldTraceV2.BatchOps
          (AspisR1FastDotsOuterFoldTraceV2.LimbOps ops))
        a g slot it it' limbs limbs' hstep4 hbody
      rcases hadv with ⟨start, hnext, hstartEq, hcursorBody, hendBody, hstepBody⟩
      have hpair : (some hbatch.start, it') = (some start, it') :=
        Result.ok.inj (hbatch.next.symm.trans hnext)
      have hstartBatch : hbatch.start = it.iter.start :=
        (Option.some.inj (congrArg Prod.fst hpair)).trans hstartEq
      have haddSpec : UScalar.add hbatch.start 4#usize
          ⦃z => z.val = hbatch.start.val + 4⦄ := by
        apply UScalar.add_spec
        scalar_tac
      obtain ⟨z, hz, hzval⟩ := WP.spec_imp_exists haddSpec
      have hzeq : z = hbatch.batchEndArg := Result.ok.inj (hz.symm.trans hbatch.add4)
      have hbatchEndVal : hbatch.batchEndArg.val = it.iter.start.val + 4 := by
        have hzval' := hzval
        rw [hzeq, hstartBatch] at hzval'
        exact hzval'
      have hminEq : hbatch.rangeEnd =
          if hbatch.batchEndArg < 26#usize then hbatch.batchEndArg else 26#usize := by
        simpa [core.cmp.min, core.cmp.OrdUsize, core.cmp.impls.OrdUsize.min] using hbatch.min26.symm
      have hrangeMin : hbatch.rangeEnd.val = min (it.iter.start.val + 4) 26 := by
        by_cases hlt : hbatch.batchEndArg < 26#usize
        · have hrangeUsize : hbatch.rangeEnd = hbatch.batchEndArg := by
            rw [hminEq]
            simp [hlt]
          have hminVal : hbatch.rangeEnd.val = hbatch.batchEndArg.val :=
            congrArg UScalar.val hrangeUsize
          have hltNat : it.iter.start.val + 4 < 26 := by
            rw [← hbatchEndVal]
            scalar_tac
          rw [hbatchEndVal] at hminVal
          omega
        · have hrangeUsize : hbatch.rangeEnd = 26#usize := by
            rw [hminEq]
            simp [hlt]
          have hminVal : hbatch.rangeEnd.val = 26 := by
            simpa using congrArg UScalar.val hrangeUsize
          have hge : 26 ≤ it.iter.start.val + 4 := by
            rw [← hbatchEndVal]
            scalar_tac
          omega
      have hcursor' : it'.iter.start.val = min (it.iter.start.val + 4) 26 := by
        simpa [hstepVal, hend26] using hcursor
      have hrangeNext : hbatch.rangeEnd.val = it'.iter.start.val := hrangeMin.trans hcursor'.symm
      have hcs : cs.map (fun c => c.term.val) =
          List.range' it.iter.start.val (it'.iter.start.val - it.iter.start.val) := by
        have hindices := AspisR1FastDotsActualTermGeometryRootV1.actual_trace_term_indices
          (AspisR1FastDotsOuterFoldTraceV2.ActualOps ops) a g slot
          {start := hbatch.start, «end» := hbatch.rangeEnd}
          (Array.repeat 8#usize 0#u64) hbatch.sums cs hbatch.sourceTrace
        simpa [hstartBatch, hrangeNext] using hindices
      have hendNext : it'.iter.end.val = 26 := by rw [hend]; exact hend26
      have htailIndices := ih hendNext
      have hbounds : it.iter.start.val ≤ it'.iter.start.val ∧ it'.iter.start.val ≤ 26 := by
        rw [hcursor']
        constructor
        · apply (Nat.le_min).2
          constructor <;> omega
        · exact Nat.min_le_right _ _
      have hlength :
          (it'.iter.start.val - it.iter.start.val) + (26 - it'.iter.start.val) =
            26 - it.iter.start.val := by omega
      simp only [List.flatten_cons, List.map_append, hcs, htailIndices]
      have hsplit : it.iter.start.val + (it'.iter.start.val - it.iter.start.val) =
          it'.iter.start.val := by omega
      have hfirst :
          it.iter.start.val + (it'.iter.start.val - it.iter.start.val) - it.iter.start.val =
            it'.iter.start.val - it.iter.start.val := by omega
      have hlast :
          26 - (it.iter.start.val + (it'.iter.start.val - it.iter.start.val)) =
            26 - it'.iter.start.val := by omega
      calc
        List.range' it.iter.start.val (it'.iter.start.val - it.iter.start.val) ++
            List.range' it'.iter.start.val (26 - it'.iter.start.val) =
            List.range' it.iter.start.val
              ((it'.iter.start.val - it.iter.start.val) + (26 - it'.iter.start.val)) := by
                rw [← hsplit, hfirst, hlast, List.range'_append_1]
        _ = List.range' it.iter.start.val (26 - it.iter.start.val) := by rw [hlength]

/-- A successful generated four-slot callback keeps the exact ordered term
    coverage and byte/parser witnesses for the same seven-batch trace used in
    the decoded-value theorem. -/
theorem callback_trace_exact_source_coverage
    (base ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (value : Wide)
    (h : CallbackDecodedTrace base ops a g slot value) :
    ∃ ds : List (List Contribution),
      CallbackDecodedTrace base ops a g slot value ∧
      ds.flatten.map (fun c => c.term.val) = List.range' 0 26 ∧
      ∀ c ∈ ds.flatten, SourceMeaning a g slot c := by
  rcases h with ⟨ds,starts,limbs,body,tailValue,wide28,q,tailStart,tail2,cs,
    hcb,htrace,hseven,hfirstQuery,hwide28,hrun,hfinish,haccepted,hproduct,
    hfinishWords,hresult⟩
  have hstart : AspisR1FastDotsStepSchedule.startBy.iter.start.val = 0 := by
    norm_num [AspisR1FastDotsStepSchedule.startBy, AspisR1FastDotsStepSchedule.startRange]
  have hend : AspisR1FastDotsStepSchedule.startBy.iter.end.val = 26 := by
    norm_num [AspisR1FastDotsStepSchedule.startBy, AspisR1FastDotsStepSchedule.startRange]
  have hindices := exact_trace_flattened_term_indices htrace hend
  refine ⟨ds, ?_, ?_, ?_⟩
  · exact ⟨ds,starts,limbs,body,tailValue,wide28,q,tailStart,tail2,cs,
      hcb,htrace,hseven,hfirstQuery,hwide28,hrun,hfinish,haccepted,hproduct,
      hfinishWords,hresult⟩
  · simpa [hstart] using hindices
  · exact exact_trace_source_meanings htrace

#print axioms exact_trace_flattened_term_indices
#print axioms callback_trace_exact_source_coverage

end AspisR1FastDotsAllFourCallbackSourceCoverageV1
