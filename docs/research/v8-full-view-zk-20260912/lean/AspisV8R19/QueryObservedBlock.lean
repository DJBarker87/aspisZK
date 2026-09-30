import AspisV8R19.QueryObservedSource
import AspisV8R19.QueryBlockStep
import AspisV8R19.SamplerObservedSqueeze

/-! Actual query squeeze/scan step with ordered successful hash observations.
No fresh-answer or independent-randomness premise is used here. -/
set_option autoImplicit false
namespace AspisV8R19.QueryObservedBlock
open Aeneas Aeneas.Std Result ControlFlow AspisR86Query
open SamplerObservation SamplerObservedLaws
open QueryChunkExecution QueryChunkModel QueryBlockWords QueryBlockStep
open DuplexFrames SourceDuplexStep SqueezeOracleBridge SqueezeSourceExecution
open SamplerObservedSqueeze (rawCalls raw_calls_decode)

theorem squeeze_execution (s : transcript.Transcript) (history : Trace) :
    QueryObservedSource.squeeze_block s history = (do
      let out ← s.hash (message s.state 1#u8)
      let next ← s.hash (message s.state 2#u8)
      ok ((out,{s with state := next}),history ++
        [(message s.state 1#u8,out),(message s.state 2#u8,next)])) := by
  have hs : s.state.val.length = 32 := s.state.property
  have ht : s.state.val.take 32 = s.state.val := List.take_of_length_le (by omega)
  simp [QueryObservedSource.squeeze_block,core.array.Array.index_mut,
    core.ops.index.IndexMutSlice,core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    Array.repeat,Array.to_slice,Slice.length,Slice.len,
    core.slice.Slice.copy_from_slice,Array.from_slice,List.setSlice!,List.slice,
    Array.update,transcript.DOM_SQUEEZE,transcript.DOM_ADVANCE,
    message,frame,Array.make,lift,bind_tc_ok,hs,List.set_append,ht,
    bind_apply,lift_apply,map_apply,observeHash,List.append_assoc]

theorem squeeze_step (H : Bytes → State) (s : State) (history : Trace) :
    QueryObservedSource.squeeze_block (queryTranscript H s) history =
      .ok ((encodeState (step H s).1,queryTranscript H (step H s).2),
        history++rawCalls H s) := by
  rw [squeeze_execution]
  simp only [queryTranscript,hashAdapter,squeeze_address,advance_address,bind_tc_ok,step,rawCalls]

theorem outer_step (H : Bytes → State) (s : State) (out : Values) (draws : Usize)
    (history : Trace) (hc : out.val.length ≤ 22) (hd : draws.val < 64) :
    ∃ out1 draws1,
      QueryObservedSource.challenge_queries_without_replacement_loop0.body
        22#usize 64#usize 262143#u32 (queryTranscript H s) out draws history =
        .ok ((if (Q22WordScan.scan (view out draws) (SamplerWords.words 18 (step H s).1)).2
          then .done (queryTranscript H (step H s).2,out1)
          else .cont (queryTranscript H (step H s).2,out1,draws1)),history++rawCalls H s) ∧
      view out1 draws1 = (Q22WordScan.scan (view out draws) (SamplerWords.words 18 (step H s).1)).1 ∧
      out1.val.length ≤ 22 ∧ draws1.val ≤ 64 := by
  obtain ⟨out1,draws1,he,hv,hc1,hd1⟩ := QueryChunkSource.source_scan_bounded
    262143#u32 (blockWords (step H s).1) emptySlice out draws hc (by omega)
  simp only [candidates_exact] at he hv
  refine ⟨out1,draws1,?_,hv,hc1,hd1⟩
  have hd' : draws < 64#usize := hd
  simp only [QueryObservedSource.challenge_queries_without_replacement_loop0.body,
    if_pos hd',bind_apply,lift_apply,squeeze_step,bind_tc_ok,lift,chunks_success,he]
  cases hs : (Q22WordScan.scan (view out draws) (SamplerWords.words 18 (step H s).1)).2 <;> rfl

theorem exhausted_step (self : transcript.Transcript) (out : Values) (draws : Usize)
    (history : Trace) (hd : 64 ≤ draws.val) :
    QueryObservedSource.challenge_queries_without_replacement_loop0.body
      22#usize 64#usize 262143#u32 self out draws history = .ok (.done (self,out),history) := by
  have hd' : ¬ draws < 64#usize := by change ¬ draws.val < 64; omega
  simp only [QueryObservedSource.challenge_queries_without_replacement_loop0.body,if_neg hd',pure_apply]

#print axioms squeeze_execution
#print axioms squeeze_step
#print axioms outer_step
#print axioms exhausted_step
end AspisV8R19.QueryObservedBlock
