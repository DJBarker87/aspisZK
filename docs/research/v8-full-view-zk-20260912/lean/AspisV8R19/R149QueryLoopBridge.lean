import AspisV8R19.R148QueryBlockBridge
import AspisV8R19.Q22SamplerProgram

/-! Mechanical adaptation of the source execution induction to the exact
R137 generated outer loop, retaining the original SourceExec/bound premises. -/
set_option autoImplicit false
namespace AspisV8R19.R149QueryLoopBridge
open Aeneas Aeneas.Std Result ControlFlow AspisR86Query
open AspisV8R19.QueryChunkExecution AspisV8R19.QueryChunkModel
open AspisV8R19.Q22SamplerProgram AspisV8R19.Q22WordScan

abbrev Bytes := AspisV8R19.DuplexFrames.Bytes
abbrev State := AspisV8R19.SourceDuplexStep.State
abbrev Values := AspisV8R19.QueryChunkExecution.Values

def queryTranscript (H : Bytes → State) (s : State) :
    AspisR137Q22.transcript.Transcript :=
  AspisV8R19.R148QueryBlockBridge.queryTranscript H s

theorem execution_of_model (H : Bytes → State) {s : State}
    {q : ScanState}
    {v : AspisV8R19.MemoizedProgramLaw.View Bytes State AspisV8R19.Q22SamplerProgram.Result}
    (run : AspisV8R19.Q22SamplerProgram.SourceExec H s q v)
    (out : Values) (draws : Usize) (hv : view out draws = q)
    (hc : out.val.length ≤ 22) (hd : draws.val ≤ 64) :
    ∃ finalOut,
      AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0
        (queryTranscript H s) 22#usize 64#usize 262143#u32 out draws =
        .ok (queryTranscript H v.2.2,finalOut) ∧
      AspisV8R19.Q22WordScan.finish (view finalOut 0#usize) = v.2.1 ∧
      finalOut.val.length ≤ 22 := by
  induction run generalizing out draws with
  | done s q cap =>
      have cap' : 64 ≤ draws.val := by simpa [← hv,view] using cap
      refine ⟨out,?_,?_,hc⟩
      · rw [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0,
          loop.eq_def]
        simp only [AspisV8R19.R148QueryBlockBridge.exhausted_step _ _ _ cap']
      · simp [← hv,AspisV8R19.Q22WordScan.finish,view]
  | stop s q draw stop =>
      have draw' : draws.val < 64 := by simpa [← hv,view] using draw
      obtain ⟨out1,draws1,he,hv1,hc1,hd1⟩ :=
        AspisV8R19.R148QueryBlockBridge.outer_step H s out draws hc draw'
      simp only [hv,stop,↓reduceIte] at he hv1
      refine ⟨out1,?_,?_,hc1⟩
      · rw [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0,
          loop.eq_def]
        simp only [queryTranscript,he]
      · have hf := congrArg AspisV8R19.Q22WordScan.finish hv1
        simpa only [AspisV8R19.Q22WordScan.finish,view] using hf
  | more s q draw keepGoing tail rest ih =>
      have draw' : draws.val < 64 := by simpa [← hv,view] using draw
      obtain ⟨out1,draws1,he,hv1,hc1,hd1⟩ :=
        AspisV8R19.R148QueryBlockBridge.outer_step H s out draws hc draw'
      simp only [hv,keepGoing,Bool.false_eq_true,↓reduceIte] at he hv1
      obtain ⟨finalOut,heFinal,hfFinal,hcFinal⟩ := ih out1 draws1 hv1 hc1 hd1
      refine ⟨finalOut,?_,hfFinal,hcFinal⟩
      rw [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0,
        loop.eq_def]
      simp only [queryTranscript,he]
      simpa only [AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0,
        queryTranscript]
        using heFinal

theorem source_loop (H : Bytes → State) (n : Nat) (s : State)
    (out : Values) (draws : Usize) (hc : out.val.length ≤ 22)
    (hd : draws.val ≤ 64) (enough : 64 ≤ draws.val + 8*n) :
    ∃ finalOut,
      AspisR137Q22.transcript.Transcript.challenge_queries_without_replacement_loop0
        (queryTranscript H s) 22#usize 64#usize 262143#u32 out draws =
        .ok (queryTranscript H (AspisV8R19.Q22SamplerProgram.loopRun H n s (view out draws)).2.2,finalOut) ∧
      AspisV8R19.Q22WordScan.finish (view finalOut 0#usize) =
        (AspisV8R19.Q22SamplerProgram.loopRun H n s (view out draws)).2.1 ∧
      finalOut.val.length ≤ 22 := by
  exact execution_of_model H
    (AspisV8R19.Q22SamplerProgram.sufficient_fuel_source_exec H n s (view out draws) enough)
    out draws rfl hc hd

#print axioms execution_of_model
#print axioms source_loop
end AspisV8R19.R149QueryLoopBridge
