import FSV8FiniteInterpreterPMFBridge

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8FiniteInterpreterEventBridge
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8PostOODGammaScript FSV8FiniteInterpreterBridge
open FSV8FiniteInterpreterPMFBridge
open AspisK1.V7Tag73AdaptiveLazyOracle

abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev Output :=
  Option (Except (Sum FSOODSampler.Error FSNonzeroQM31.Error)
    (OODResult × Gamma) × Block) × FSBoundedTranscript.Oracle

def currentOutputEvent {n m steps : Nat}
    (fallback : Block) (firstWork : Point → Script (List UInt8) Block Unit n)
    (secondWork : Point → Point → Script (List UInt8) Block Unit m)
    (body : List UInt8) (digest : Block) (event : Output → Prop) :
    FreshAnswerTape Block steps → Prop :=
  fun tape => event (finiteInterpreterV7Map fallback firstWork secondWork body digest tape)

theorem currentOutputEvent_probability_eq {n m steps : Nat}
    (fallback : Block) (firstWork : Point → Script (List UInt8) Block Unit n)
    (secondWork : Point → Point → Script (List UInt8) Block Unit m)
    (body : List UInt8) (digest : Block) (event : Output → Prop)
    [DecidablePred event] :
    (finiteInterpreterDistribution (steps := steps)
      fallback firstWork secondWork body digest).toOuterMeasure
        {output | event output} =
      (PMF.uniformOfFintype (FreshAnswerTape Block steps)).toOuterMeasure
        {tape | currentOutputEvent fallback firstWork secondWork body digest event tape} := by
  rw [finiteInterpreterDistribution_eq_v7_uniform (steps := steps)]
  rw [PMF.toOuterMeasure_map_apply]
  rfl

theorem currentOutputEvent_probability_eq_pullback {n m steps : Nat}
    (fallback : Block) (firstWork : Point → Script (List UInt8) Block Unit n)
    (secondWork : Point → Point → Script (List UInt8) Block Unit m)
    (body : List UInt8) (digest : Block) (event : Output → Prop)
    [DecidablePred event] :
    (finiteInterpreterDistribution (steps := steps)
      fallback firstWork secondWork body digest).toOuterMeasure
        {output | event output} =
      ((PMF.uniformOfFintype (FreshAnswerTape Block steps)).map
        (finiteInterpreterV7Map fallback firstWork secondWork body digest)).toOuterMeasure
        {output | event output} := by
  rw [finiteInterpreterDistribution_eq_v7_uniform (steps := steps)]

/- The V7 `controllerFromFreshAnswerTape` consumes an `OracleState` through its
   `AdaptiveController` interface, whereas the current script interpreter
   consumes `FSOracleExecution.State` directly.  The output event theorem above
   is therefore the exact available interface bridge; no source/event coupling
   is asserted here. -/
#print axioms currentOutputEvent_probability_eq
#print axioms currentOutputEvent_probability_eq_pullback
end AspisV8Completion.FSV8FiniteInterpreterEventBridge
