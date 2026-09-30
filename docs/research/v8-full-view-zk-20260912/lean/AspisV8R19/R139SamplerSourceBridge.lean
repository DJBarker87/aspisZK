import AspisV8R19.R137NonzeroLoop

/-! Release-facing aliases for the exact R137 sampler source bridge.  The
first theorem reaches the complete four-limb QM31 challenge; the second
unfolds the actual three-attempt nonzero wrapper.  The remaining model/trace
correspondence for that wrapper is intentionally not claimed here. -/
set_option autoImplicit false
namespace AspisV8R19.R139SamplerSourceBridge

open Aeneas Aeneas.Std Result AspisR137Transcript
open DuplexFrames SourceDuplexStep

theorem qm31_source_exact (H : Bytes → State) (s : State) :
    transcript.Transcript.challenge_qm31
        (R137TranscriptPrimitiveBridge.transcriptFor H s) =
      .ok (R137SamplerChallengeBridge.encodeResult
          (QM31SamplerProgram.challengeRun H s).2.1,
        R137TranscriptPrimitiveBridge.transcriptFor H
          (QM31SamplerProgram.challengeRun H s).2.2) :=
  R137SamplerChallengeBridge.challenge_exact H s

theorem nonzero_source_unfolds (s : transcript.Transcript) :
    transcript.Transcript.challenge_nonzero_qm31 s =
      R137NonzeroLoop.bounded 3 s :=
  R137NonzeroLoop.entry_three s

#print axioms qm31_source_exact
#print axioms nonzero_source_unfolds

end AspisV8R19.R139SamplerSourceBridge
