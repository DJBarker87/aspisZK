import FSV8FiniteInterpreterBridge

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8FiniteInterpreterPMFBridge
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8PostOODGammaScript FSV8FiniteInterpreterBridge
open FSV8V7FiniteUniformBridge
open AspisK1.V7Tag73AdaptiveLazyOracle

abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point

noncomputable def finiteInterpreterV7Map {n m steps : Nat}
    (fallback : Block) (firstWork : Point → Script (List UInt8) Block Unit n)
    (secondWork : Point → Point → Script (List UInt8) Block Unit m)
    (body : List UInt8) (digest : Block) :
    FreshAnswerTape Block steps →
      (Option (Except (Sum FSOODSampler.Error FSNonzeroQM31.Error)
        (OODResult × Gamma) × Block) × FSBoundedTranscript.Oracle) :=
  finiteInterpreterMap fallback firstWork secondWork body digest ∘
    (finFreshEquiv steps).symm

theorem finiteInterpreterDistribution_eq_v7_uniform {n m steps : Nat}
    (fallback : Block) (firstWork : Point → Script (List UInt8) Block Unit n)
    (secondWork : Point → Point → Script (List UInt8) Block Unit m)
    (body : List UInt8) (digest : Block) :
    finiteInterpreterDistribution (steps := steps)
        fallback firstWork secondWork body digest =
      (PMF.uniformOfFintype (FreshAnswerTape Block steps)).map
        (finiteInterpreterV7Map fallback firstWork secondWork body digest) := by
  unfold finiteInterpreterDistribution finiteInterpreterV7Map
  rw [← uniform_finFreshEquiv]
  rw [PMF.map_comp]
  congr 1
  funext finite
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

#print axioms finiteInterpreterDistribution_eq_v7_uniform
end AspisV8Completion.FSV8FiniteInterpreterPMFBridge
