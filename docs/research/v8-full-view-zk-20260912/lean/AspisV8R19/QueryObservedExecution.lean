import AspisV8R19.QueryObservedBlock
import AspisV8R19.QueryEntryExecution

/-! Complete observed execution of the actual selected query entry. Bounded
progress is discharged by the existing source relation; no artificial cutoff
or replacement sampler is inserted. -/
set_option autoImplicit false
namespace AspisV8R19.QueryObservedExecution
open Aeneas Aeneas.Std Result ControlFlow AspisR86Query
open SamplerObservation SamplerObservedLaws
open QueryChunkExecution QueryChunkModel QueryBlockStep QueryObservedBlock
open DuplexFrames SourceDuplexStep
open SamplerObservedSqueeze (rawCalls raw_calls_decode)
open QueryEntryExecution (finishSource)

theorem execution_of_model (H : Bytes → State) {s : State}
    {q : Q22WordScan.ScanState}
    {v : MemoizedProgramLaw.View Bytes State Q22SamplerProgram.Result}
    (run : Q22SamplerProgram.SourceExec H s q v)
    (out : Values) (draws : Usize) (hv : view out draws = q)
    (hc : out.val.length ≤ 22) (hd : draws.val ≤ 64) (history : Trace) :
    ∃ finalOut observed,
      QueryObservedSource.challenge_queries_without_replacement_loop0
        (queryTranscript H s) 22#usize 64#usize 262143#u32 out draws history =
        .ok ((queryTranscript H v.2.2,finalOut),observed) ∧
      Q22WordScan.finish (view finalOut 0#usize) = v.2.1 ∧
      finalOut.val.length ≤ 22 ∧ decodeTrace observed=decodeTrace history++v.1 := by
  induction run generalizing out draws history with
  | done s q cap =>
      have cap' : 64 ≤ draws.val := by simpa [← hv,view] using cap
      refine ⟨out,history,?_,?_,hc,by simp⟩
      · rw [QueryObservedSource.challenge_queries_without_replacement_loop0,loop_unfold]
        simp only [QueryObservedBlock.exhausted_step _ _ _ _ cap',bind_tc_ok]
      · simp [← hv,Q22WordScan.finish,view]
  | stop s q draw stop =>
      have draw' : draws.val < 64 := by simpa [← hv,view] using draw
      obtain ⟨out1,draws1,he,hv1,hc1,hd1⟩ := QueryObservedBlock.outer_step H s out draws history hc draw'
      simp only [hv,stop,↓reduceIte] at he hv1
      refine ⟨out1,history++rawCalls H s,?_,?_,hc1,?_⟩
      · rw [QueryObservedSource.challenge_queries_without_replacement_loop0,loop_unfold]
        simp only [he,bind_tc_ok]
      · have hf := congrArg Q22WordScan.finish hv1
        simpa only [Q22WordScan.finish,view] using hf
      · simp only [decode_append,raw_calls_decode]
  | more s q draw keepGoing tail rest ih =>
      have draw' : draws.val < 64 := by simpa [← hv,view] using draw
      obtain ⟨out1,draws1,he,hv1,hc1,hd1⟩ := QueryObservedBlock.outer_step H s out draws history hc draw'
      simp only [hv,keepGoing,Bool.false_eq_true,↓reduceIte] at he hv1
      obtain ⟨finalOut,observed,heFinal,hfFinal,hcFinal,ht⟩ :=
        ih out1 draws1 hv1 hc1 hd1 (history++rawCalls H s)
      refine ⟨finalOut,observed,?_,hfFinal,hcFinal,?_⟩
      · rw [QueryObservedSource.challenge_queries_without_replacement_loop0,loop_unfold]
        simp only [he,bind_tc_ok]
        simpa only [QueryObservedSource.challenge_queries_without_replacement_loop0]
          using heFinal
      · simpa only [decode_append,raw_calls_decode,List.append_assoc] using ht

theorem selected_entry (self : transcript.Transcript) (history : Trace) :
    QueryObservedSource.query_probe self history = (do
      let ((next,out),t) ← QueryObservedSource.challenge_queries_without_replacement_loop0
        self 22#usize 64#usize 262143#u32 (alloc.vec.Vec.with_capacity U32 22#usize) 0#usize history
      ok ((finishSource out,next),t)) := by
  have hs : (1#u32 <<< 18#i32) = .ok 262144#u32 := by rfl
  have hd : ((262144#u32 - 1#u32) : Result U32) = .ok 262143#u32 := by rfl
  simp [QueryObservedSource.query_probe,hs,QueryObservedSource.challenge_queries_without_replacement,
    hd,lift,finishSource,bind_apply,lift_apply]
  intro next out t _
  split_ifs <;> rfl

theorem public_result (H : Bytes → State) (s : State) (history : Trace) :
    ∃ out : Values, ∃ observed,
      QueryObservedSource.query_probe (queryTranscript H s) history =
        .ok ((finishSource out,queryTranscript H (Q22SamplerProgram.challengeRun H s).2.2),observed) ∧
      Q22WordScan.finish (view out 0#usize) = (Q22SamplerProgram.challengeRun H s).2.1 ∧
      out.val.length ≤ 22 ∧
      decodeTrace observed=decodeTrace history++(Q22SamplerProgram.challengeRun H s).1 := by
  obtain ⟨out,observed,he,hf,hc,ht⟩ := execution_of_model H
    (Q22SamplerProgram.no_artificial_cutoff H s)
    (alloc.vec.Vec.with_capacity U32 22#usize) 0#usize rfl (by decide) (by decide) history
  refine ⟨out,observed,?_,hf,hc,ht⟩
  rw [selected_entry,he]
  rfl

theorem public_erasure (H : Bytes → State) (s : State) (history : Trace) :
    (do let (out,_) ← QueryObservedSource.query_probe (queryTranscript H s) history
        ok out) = query_probe (queryTranscript H s) := by
  obtain ⟨out,t,he,hf,hc,ht⟩ := public_result H s history
  obtain ⟨out1,he1,hf1,hc1⟩ := QueryEntryExecution.public_result H s
  rw [he,he1]
  simp only [bind_tc_ok]
  have same : finishSource out = finishSource out1 := by
    have hh := hf.trans hf1.symm
    unfold Q22WordScan.finish view at hh
    unfold finishSource
    split_ifs with h h1 h1
    · have hx : out=out1 := by
        apply Subtype.ext
        have hh1 : out.val.map UScalar.val=out1.val.map UScalar.val := by
          simpa only [List.length_map,show out.val.length=22 from congrArg UScalar.val h,
            show out1.val.length=22 from congrArg UScalar.val h1,↓reduceIte,Except.ok.injEq] using hh
        exact (List.map_inj_right (fun _ _ h => UScalar.eq_of_val_eq h)).mp hh1
      rw [hx]
    · have hv : out1.val.length≠22 := by intro h;apply h1;apply UScalar.eq_of_val_eq;exact h
      simp only [List.length_map,show out.val.length=22 from congrArg UScalar.val h,
        if_neg hv] at hh
      cases hh
    · have hv : out.val.length≠22 := by intro h1;apply h;apply UScalar.eq_of_val_eq;exact h1
      simp only [List.length_map,show out1.val.length=22 from congrArg UScalar.val h1,
        if_neg hv] at hh
      cases hh
    · have hv : out.val.length≠22 := by intro h1;apply h;apply UScalar.eq_of_val_eq;exact h1
      have hv1 : out1.val.length≠22 := by intro h;apply h1;apply UScalar.eq_of_val_eq;exact h
      have eqn : alloc.vec.Vec.len out=alloc.vec.Vec.len out1 := by
        apply UScalar.eq_of_val_eq
        change out.val.length=out1.val.length
        simpa only [List.length_map,if_neg hv,if_neg hv1,Except.error.injEq] using hh
      rw [eqn]
  rw [same]

#print axioms execution_of_model
#print axioms selected_entry
#print axioms public_result
#print axioms public_erasure
end AspisV8R19.QueryObservedExecution
