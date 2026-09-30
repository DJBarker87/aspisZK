import AspisV8R19.QueryObservedExecution
import AspisV8R19.CachedFiniteSupport

/-! Complete selected q22 public view and its memoized ideal-oracle law.
Arbitrary prior cached answers, repeated queries, stopping and exhaustion
remain visible. This is not a whole-protocol privacy or soundness theorem. -/
set_option autoImplicit false
namespace AspisV8R19.QueryObservedProgram
open Aeneas Aeneas.Std Result AspisR86Query
open SamplerObservation DuplexFrames SourceDuplexStep SqueezeOracleBridge
open QueryBlockStep QueryEntryExecution
open MemoizedProgramLaw OracleFiniteSupport OracleResampling
noncomputable section

def observe (H : Bytes → State) (s : State) (history : Trace) := do
  let ((result,next),t) ← QueryObservedSource.query_probe (queryTranscript H s) history
  ok (decodeTrace t,(decodeResult result,decodeState next.state))

theorem public_view (H : Bytes → State) (s : State) (history : Trace) :
    observe H s history = .ok (decodeTrace history++(Q22SamplerProgram.challengeRun H s).1,
      (Q22SamplerProgram.challengeRun H s).2) := by
  obtain ⟨out,t,he,hf,_,ht⟩ := QueryObservedExecution.public_result H s history
  unfold observe
  erw [he]
  simp only [bind_tc_ok,ht,decode_finish,hf,queryTranscript,state_roundtrip]

theorem oracle_program (H : Bytes → State) (s : State) :
    observe H s [] = .ok (eval H (Q22SamplerProgram.challengeProgram s)) := by
  rw [public_view,Q22SamplerProgram.challenge_exact]
  simp only [decodeTrace,List.map_nil,List.nil_append]

theorem value_state_erasure (H : Bytes → State) (s : State) (history : Trace) :
    (do let (_,out) ← observe H s history; ok out) = QueryEntryExecution.run H s := by
  rw [public_view,QueryEntryExecution.public_value_state]
  rfl

theorem cached_oracle_law (s : State) (t : AspisV8PairedCommitment.Table Bytes State)
    (fallback : State) (test : Result (View Bytes State Q22SamplerProgram.Result) → ℚ) :
    mean (fun H : {i // i ∈ support (Q22SamplerProgram.challengeProgram s)} → State =>
      test (observe (complete t (extend (support (Q22SamplerProgram.challengeProgram s)) H fallback)) s [])) =
      lazyMean (Q22SamplerProgram.challengeProgram s) t (fun view => test (.ok view)) := by
  simp only [oracle_program]
  exact CachedFiniteSupport.own_support_law (I := Bytes) (A := State)
    (O := Q22SamplerProgram.Result) (Q22SamplerProgram.challengeProgram s) t fallback
    (fun view => test (.ok view))

#print axioms public_view
#print axioms oracle_program
#print axioms value_state_erasure
#print axioms cached_oracle_law
end
end AspisV8R19.QueryObservedProgram
