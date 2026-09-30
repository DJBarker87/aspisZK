import AspisV8R19.QueryEntrySource
import AspisV8R19.QueryLoopExecution

/-! Actual selected public entry, including its explicit argument guard.
This is a value/state theorem, not yet the observed shared-oracle history. -/
set_option autoImplicit false
namespace AspisV8R19.QueryEntryExecution
open Aeneas Aeneas.Std Result AspisR86Query
open QueryChunkExecution QueryChunkModel QueryBlockStep QueryLoopExecution
open DuplexFrames SourceDuplexStep SqueezeOracleBridge

def finishSource (out : Values) : core.result.Result Values transcript.QuerySampleError :=
  if alloc.vec.Vec.len out = 22#usize then .Ok out
  else .Err (.DrawLimitExhausted (alloc.vec.Vec.len out) 64#usize)

theorem selected_entry (self : transcript.Transcript) :
    query_probe self = (do
      let (next,out) ← transcript.Transcript.challenge_queries_without_replacement_loop0
        self 22#usize 64#usize 262143#u32 (alloc.vec.Vec.with_capacity U32 22#usize) 0#usize
      ok (finishSource out,next)) := by
  have hs : (1#u32 <<< 18#i32) = .ok 262144#u32 := by rfl
  have hd : ((262144#u32 - 1#u32) : Result U32) = .ok 262143#u32 := by rfl
  simp [query_probe,hs,transcript.Transcript.challenge_queries_without_replacement,
    hd,lift,finishSource]
  intro next out _
  split_ifs <;> rfl

theorem public_result (H : Bytes → State) (s : State) :
    ∃ out : Values,
      query_probe (queryTranscript H s) =
        .ok (finishSource out,queryTranscript H (Q22SamplerProgram.challengeRun H s).2.2) ∧
      Q22WordScan.finish (view out 0#usize) = (Q22SamplerProgram.challengeRun H s).2.1 ∧
      out.val.length ≤ 22 := by
  obtain ⟨out,he,hf,hc⟩ := QueryLoopExecution.source_loop H 8 s
    (alloc.vec.Vec.with_capacity U32 22#usize) 0#usize (by decide) (by decide) (by decide)
  refine ⟨out,?_,hf,hc⟩
  rw [selected_entry,he]
  rfl

def decodeResult : core.result.Result Values transcript.QuerySampleError → Except Nat (List Nat)
  | .Ok out => .ok (out.val.map UScalar.val)
  | .Err (.DrawLimitExhausted n _) => .error n.val
  | .Err _ => .error 0

theorem decode_finish (out : Values) :
    decodeResult (finishSource out) = Q22WordScan.finish (view out 0#usize) := by
  by_cases h : alloc.vec.Vec.len out = 22#usize
  · have hv : out.val.length=22 := congrArg UScalar.val h
    rw [finishSource,if_pos h]
    simp only [decodeResult,Q22WordScan.finish,view,List.length_map,hv,↓reduceIte]
  · have hv : out.val.length≠22 := by
      intro he;apply h;apply UScalar.eq_of_val_eq;exact he
    rw [finishSource,if_neg h]
    simp only [decodeResult,Q22WordScan.finish,view,List.length_map,if_neg hv]
    rfl

def run (H : Bytes → State) (s : State) := do
  let (result,next) ← query_probe (queryTranscript H s)
  ok (decodeResult result,decodeState next.state)

theorem public_value_state (H : Bytes → State) (s : State) :
    run H s = .ok (Q22SamplerProgram.challengeRun H s).2 := by
  obtain ⟨out,he,hf,_⟩ := QueryLoopExecution.source_loop H 8 s
    (alloc.vec.Vec.with_capacity U32 22#usize) 0#usize (by decide) (by decide) (by decide)
  simp only [run,selected_entry,he,bind_tc_ok,decode_finish]
  change Q22WordScan.finish (view out 0#usize) = (Q22SamplerProgram.challengeRun H s).2.1 at hf
  change Result.ok (Q22WordScan.finish (view out 0#usize),
    decodeState (queryTranscript H (Q22SamplerProgram.challengeRun H s).2.2).state) = _
  simp only [hf,queryTranscript,state_roundtrip]

#print axioms selected_entry
#print axioms public_result
#print axioms decode_finish
#print axioms public_value_state
end AspisV8R19.QueryEntryExecution
