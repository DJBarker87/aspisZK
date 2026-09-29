import AspisV8R19.QueryBlockStep
import AspisV8R19.Q22SamplerProgram

/-! Value/state correspondence for the actual extracted outer query loop.
The model's proved finite bound discharges termination, without supplying
an artificial fuel result to the Rust loop. The public guard and an observed
shared-oracle execution theorem remain separate obligations. -/
set_option autoImplicit false
namespace AspisV8R19.QueryLoopExecution
open Aeneas Aeneas.Std Result ControlFlow AspisR86Query
open QueryChunkExecution QueryChunkModel QueryBlockStep
open DuplexFrames SourceDuplexStep

theorem execution_of_model (H : Bytes → State) {s : State}
    {q : Q22WordScan.ScanState}
    {v : MemoizedProgramLaw.View Bytes State Q22SamplerProgram.Result}
    (run : Q22SamplerProgram.SourceExec H s q v)
    (out : Values) (draws : Usize) (hv : view out draws = q)
    (hc : out.val.length ≤ 22) (hd : draws.val ≤ 64) :
    ∃ finalOut,
      transcript.Transcript.challenge_queries_without_replacement_loop0
        (queryTranscript H s) 22#usize 64#usize 262143#u32 out draws =
        .ok (queryTranscript H v.2.2,finalOut) ∧
      Q22WordScan.finish (view finalOut 0#usize) = v.2.1 ∧
      finalOut.val.length ≤ 22 := by
  induction run generalizing out draws with
  | done s q cap =>
      have cap' : 64 ≤ draws.val := by simpa [← hv,view] using cap
      refine ⟨out,?_,?_,hc⟩
      · rw [transcript.Transcript.challenge_queries_without_replacement_loop0,loop.eq_def]
        simp only [exhausted_step _ _ _ cap']
      · simp [← hv,Q22WordScan.finish,view]
  | stop s q draw stop =>
      have draw' : draws.val < 64 := by simpa [← hv,view] using draw
      obtain ⟨out1,draws1,he,hv1,hc1,hd1⟩ := outer_step H s out draws hc draw'
      simp only [hv,stop,↓reduceIte] at he hv1
      refine ⟨out1,?_,?_,hc1⟩
      · rw [transcript.Transcript.challenge_queries_without_replacement_loop0,loop.eq_def]
        simp only [he]
      · have hf := congrArg Q22WordScan.finish hv1
        simpa only [Q22WordScan.finish,view] using hf
  | more s q draw keepGoing tail rest ih =>
      have draw' : draws.val < 64 := by simpa [← hv,view] using draw
      obtain ⟨out1,draws1,he,hv1,hc1,hd1⟩ := outer_step H s out draws hc draw'
      simp only [hv,keepGoing,Bool.false_eq_true,↓reduceIte] at he hv1
      obtain ⟨finalOut,heFinal,hfFinal,hcFinal⟩ := ih out1 draws1 hv1 hc1 hd1
      refine ⟨finalOut,?_,hfFinal,hcFinal⟩
      rw [transcript.Transcript.challenge_queries_without_replacement_loop0,loop.eq_def]
      simp only [he]
      simpa only [transcript.Transcript.challenge_queries_without_replacement_loop0]
        using heFinal

theorem source_loop (H : Bytes → State) (n : Nat) (s : State)
    (out : Values) (draws : Usize) (hc : out.val.length ≤ 22)
    (hd : draws.val ≤ 64) (enough : 64 ≤ draws.val + 8*n) :
    ∃ finalOut,
      transcript.Transcript.challenge_queries_without_replacement_loop0
        (queryTranscript H s) 22#usize 64#usize 262143#u32 out draws =
        .ok (queryTranscript H (Q22SamplerProgram.loopRun H n s (view out draws)).2.2,finalOut) ∧
      Q22WordScan.finish (view finalOut 0#usize) =
        (Q22SamplerProgram.loopRun H n s (view out draws)).2.1 ∧
      finalOut.val.length ≤ 22 := by
  exact execution_of_model H
    (Q22SamplerProgram.sufficient_fuel_source_exec H n s (view out draws) enough)
    out draws rfl hc hd

#print axioms execution_of_model
#print axioms source_loop
end AspisV8R19.QueryLoopExecution
