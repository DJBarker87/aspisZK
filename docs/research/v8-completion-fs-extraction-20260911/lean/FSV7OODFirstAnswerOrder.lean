import FSV7OODSourceAbsorbLinks

/-!
The first concrete OOD answer is joined to the next source squeeze.

This is a causal classifier, not a probability bound.  A successful source
run either exposes the authenticated answer before its digest is used as the
next squeeze state, or the full 32-byte digest was already named by an earlier
source-style squeeze input and belongs to the explicit prior-target set.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV7OODFirstAnswerOrder
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSOODSampler
open FSV7OODSampler FSV8OODBodyScript FSV7OODBodyScript
open FSV7OODSourceAbsorbLinks FSExposureOrder FSFirstFresh

abbrev Bytes := List UInt8
abbrev HashBlock := FSBoundedTranscript.Block
abbrev HashTape := FSBoundedTranscript.Tape
abbrev Point := FSV7OODBodyScript.Point
abbrev Result := FSV7OODBodyScript.Result

noncomputable section
local instance : DecidableEq Point := Classical.decEq _

/-- The first answer's actual source absorption and its subsequent squeeze are
first-exposure fresh.  Their order is correct unless the answer digest occurs
in the explicit target set preceding the absorption cut. -/
theorem successful_first_answer_order_or_prior_target {n m : Nat}
    (firstWork : Point → Script Bytes HashBlock Unit n)
    (secondWork : Point → Point → Script Bytes HashBlock Unit m)
    (body : Bytes) (digest : HashBlock) (tape : HashTape)
    (out : Result) (finalDigest : HashBlock)
    (success :
      (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
        empty).1 = some (Except.ok out, finalDigest)) :
    ∃ firstState,
      (∃ h : firstExposure
          (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
            empty).2.log
          (absorbInput firstState 62 (0 :: FSV8OODBodyScript.answerBytes body 0)) <
            (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
              empty).2.log.length,
        ((run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
          empty).2.log[firstExposure
            (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
              empty).2.log
            (absorbInput firstState 62 (0 :: FSV8OODBodyScript.answerBytes body 0))]'h).answer =
              out.afterFirstAnswer ∧
        ((run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
          empty).2.log[firstExposure
            (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
              empty).2.log
            (absorbInput firstState 62 (0 :: FSV8OODBodyScript.answerBytes body 0))]'h).fresh = true) ∧
      (∃ h : firstExposure
          (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
            empty).2.log (squeezeInput out.afterFirstAnswer) <
            (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
              empty).2.log.length,
        ((run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
          empty).2.log[firstExposure
            (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
              empty).2.log (squeezeInput out.afterFirstAnswer)]'h).fresh = true) ∧
      (firstExposure
          (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
            empty).2.log
          (absorbInput firstState 62 (0 :: FSV8OODBodyScript.answerBytes body 0)) <
        firstExposure
          (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
            empty).2.log (squeezeInput out.afterFirstAnswer) ∨
       blockBytes out.afterFirstAnswer ∈ priorTargets
          (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
            empty).2.log
          (firstExposure
            (run tape (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
              empty).2.log
            (absorbInput firstState 62 (0 :: FSV8OODBodyScript.answerBytes body 0)))) := by
  obtain ⟨firstState, _secondState, firstLinked, _secondLinked, squeezed⟩ :=
    successful_source_absorb_links firstWork secondWork body digest tape out finalDigest success
  have linkedOrder := linked_fresh_order_from_empty tape
    (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
    firstState out.afterFirstAnswer 62
    (0 :: FSV8OODBodyScript.answerBytes body 0) firstLinked squeezed
  have squeezeFresh := first_fresh_from_empty tape
    (FSV7OODBodyScript.sourceScript firstWork secondWork body digest)
    (squeezeInput out.afterFirstAnswer) squeezed
  exact ⟨firstState, linkedOrder.1, squeezeFresh, linkedOrder.2⟩

#print axioms successful_first_answer_order_or_prior_target

end
end AspisV8Completion.FSV7OODFirstAnswerOrder
