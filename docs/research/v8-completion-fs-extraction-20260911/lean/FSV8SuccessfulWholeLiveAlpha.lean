import FSLivePrefixMiddleComponents
import FSV8SuccessfulMiddleLiveAlpha

/-!
# Successful whole functional verifier constructs its live alpha execution

Starting from one successful `wholeStagedScript` run, this leaf retains the
exact source/OOD/gamma prefix, complete live-alpha middle seam and
authenticated suffix continuation.  It is deterministic and assigns no
probability law to the live challenge.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000

namespace AspisV8Completion.FSV8SuccessfulWholeLiveAlpha

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8PostOODGammaScript
open FSAuthenticatedInterleavedPrefixMiddle
open FSLivePrefixMiddleComponents
open FSV8SuccessfulMiddleLiveAlpha
open FSLiveSourceFunctionalMiddle
open FSNonzeroQM31

noncomputable section

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-- The retained source decomposition of one successful whole run.  The
middle live-alpha execution is a constructed conjunct, not an input. -/
def WholeLiveAlphaExecution {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : RootCuts) (body : Bytes) (digest : Block)
    (tape : Tape) (oracle : Oracle) (record : Record body z)
    (finalDigest : Block) : Prop :=
  ∃ staged : Partial body z, ∃ prefixDigest middleDigest,
    (run tape (sourceThenGammaScript firstWork secondWork body digest)
      oracle).1 = some (.ok (staged.out, staged.gamma), prefixDigest) ∧
    LiveAlphaExecution staged.out staged.gamma body z prefixDigest tape
      (run tape (sourceThenGammaScript firstWork secondWork body digest)
        oracle).2 staged.middle middleDigest ∧
    (run tape (suffixContinuation cuts body z middleDigest staged)
      (run tape (prefixMiddleScript firstWork secondWork z body digest)
        oracle).2).1 = some (.ok record, finalDigest)

/-- Every value in the alpha execution and both surrounding successful
continuations is constructed from the one successful whole run. -/
theorem successful_whole_constructs_live_alpha {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : RootCuts) (body : Bytes) (digest : Block)
    (tape : Tape) (oracle : Oracle) (record : Record body z)
    (finalDigest : Block)
    (success :
      (run tape (wholeStagedScript firstWork secondWork z cuts body digest)
        oracle).1 = some (.ok record, finalDigest)) :
    WholeLiveAlphaExecution firstWork secondWork z cuts body digest tape oracle
      record finalDigest := by
  rcases successful_wholeStaged_components firstWork secondWork z cuts body
      digest tape oracle record finalDigest success with
    ⟨staged, middleDigest, prefixMiddleSuccess, suffixSuccess⟩
  rcases successful_prefix_middle_components firstWork secondWork z body
      digest tape oracle staged middleDigest prefixMiddleSuccess with
    ⟨prefixDigest, sourceSuccess, middleSuccess⟩
  have liveAlpha := successful_middle_constructs_live_alpha staged.out
    staged.gamma body z prefixDigest tape
    (run tape (sourceThenGammaScript firstWork secondWork body digest)
      oracle).2 staged.middle middleDigest middleSuccess
  unfold WholeLiveAlphaExecution
  exact ⟨staged, prefixDigest, middleDigest, sourceSuccess, liveAlpha,
    suffixSuccess⟩

#print axioms successful_whole_constructs_live_alpha

end
end AspisV8Completion.FSV8SuccessfulWholeLiveAlpha
