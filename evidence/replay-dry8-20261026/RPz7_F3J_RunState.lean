import RPz7_F3J_PrefixWitness
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_RunState
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem of_run (H : Bytes → State) (code : Program Bytes State LiteralTranscript.Prefix)
    (log : List (Bytes × State)) (out : LiteralTranscript.Prefix)
    (success : eval H code=(log,out)) :
    UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix (eval H code).2)=
      UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix out) :=
  congrArg (fun r : List (Bytes × State) × LiteralTranscript.Prefix =>
    UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix r.2)) success

#print axioms of_run
end AspisR1.F3J_RunState
end
