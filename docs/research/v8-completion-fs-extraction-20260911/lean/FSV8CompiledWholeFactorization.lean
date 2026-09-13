import FSV8ExecutableWholeFactorization
import FSV8CompileScriptAlgebra

/-!
# Compiled whole-script factorization

The executable pre-alpha cut is useful to the scheduler only if compiling the
factored script gives the same oracle machine as compiling the original
selected script.  These lemmas prove that structural statement directly from
the compiler laws for `bind` and static budget padding.  They do not use
interpreter-run extensionality or add a source/freshness premise.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2400

namespace AspisV8Completion.FSV8CompiledWholeFactorization

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8V7OracleMachineBridge
open FSV8CompileScriptAlgebra
open FSV8PostOODGammaScript
open FSLiveSourceFunctionalMiddle
open FSAuthenticatedInterleavedPrefixMiddle
open FSV8ExecutablePreAlphaFactorization
open FSV8ExecutableWholeFactorization
open AspisK1.V7Tag73SharedOracleVerifierRunner

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

private theorem compile_afterFunctional_factor
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (kappa : K) (functional : SameBodyFunctionalProducerSource.Encoded)
    (functionalRun :
      SameBodyFunctionalProducerSource.fromInputs out gamma kappa body z =
        some functional)
    (digest : Block) :
    compileScript
        (bind (m := postAlphaBudget)
          (afterFunctionalPreAlphaScript out gamma body z kappa functional
            functionalRun digest) fun boundaryDraw =>
          match boundaryDraw.1 with
          | .error e => .done (Except.error e, boundaryDraw.2)
          | .ok boundary => postAlphaScript out gamma body z boundary) =
      compileScript
        (afterFunctionalScript out gamma body z kappa functional
          functionalRun digest) := by
  unfold afterFunctionalPreAlphaScript afterFunctionalScript postAlphaScript
  simp only [compileScript_bind, bindOracleMachine_assoc]
  apply congrArg (bindOracleMachine
    (compileScript (absorbScript digest 1 functional.description)))
  funext afterDescription
  apply congrArg (bindOracleMachine
    (compileScript (absorbScript afterDescription 6 functional.claim)))
  funext afterClaim
  apply congrArg (bindOracleMachine
    (compileScript (absorbScript afterClaim 1
      FSLiveSelectedMiddleQueryRho.compactFunctionalProfile)))
  funext afterImageProfile
  apply congrArg (bindOracleMachine
    (compileScript (FSNonzeroQM31.nonzeroScript 3 afterImageProfile)))
  funext tauDraw
  cases tauDraw.1 with
  | error e => rfl
  | ok tau =>
      simp only [compileScript_bind, bindOracleMachine_assoc]
      apply congrArg (bindOracleMachine
        (compileScript (absorbScript tauDraw.2 52
          (0 :: FSLiveSelectedMiddleQueryRho.response0Bytes body))))
      funext afterResponse0
      apply congrArg (bindOracleMachine
        (compileScript (absorbScript afterResponse0 20
          (0 :: FSLiveSelectedMiddleQueryRho.alpha0NonceBytes body))))
      funext afterAlphaNonce
      exact compileScript_bind _ _

private theorem compile_afterKappa_factor
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (kappa : K) (digest : Block) :
    compileScript
        (bind (m := postAlphaBudget)
          (match functionalRun :
              SameBodyFunctionalProducerSource.fromInputs out gamma kappa body z with
          | none => .done
              (Except.error FSLiveSourceFunctionalMiddle.Error.functional,
                digest)
          | some functional =>
              afterFunctionalPreAlphaScript out gamma body z kappa functional
                functionalRun digest) fun boundaryDraw =>
          match boundaryDraw.1 with
          | .error e => .done (Except.error e, boundaryDraw.2)
          | .ok boundary => postAlphaScript out gamma body z boundary) =
      compileScript
        (match functionalRun :
            SameBodyFunctionalProducerSource.fromInputs out gamma kappa body z with
        | none => .done
            (Except.error FSLiveSourceFunctionalMiddle.Error.functional,
              digest)
        | some functional =>
            afterFunctionalScript out gamma body z kappa functional
              functionalRun digest) := by
  split
  · simp only [compileScript_bind, compileScript, bindOracleMachine]
  · rename_i functional functionalRun
    exact compile_afterFunctional_factor out gamma body z kappa functional
      functionalRun digest

/-- The compiler preserves the executable middle factorization structurally;
no interpreter or tape extensionality is used. -/
theorem compile_factoredMiddleScript_eq_middleScript
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) :
    compileScript (factoredMiddleScript out gamma body z digest) =
      compileScript (middleScript out gamma body z digest) := by
  unfold factoredMiddleScript preAlphaScript middleScript
  simp only [compileScript_bind, bindOracleMachine_assoc]
  apply congrArg (bindOracleMachine
    (compileScript (absorbScript digest 50
      (FSLiveSelectedMiddleQueryRho.inactiveClaimBytes body))))
  funext afterInactive
  apply congrArg (bindOracleMachine
    (compileScript (FSNonzeroQM31.nonzeroScript 3 afterInactive)))
  funext kappaDraw
  cases kappaDraw.1 with
  | error e => rfl
  | ok kappa =>
      rw [← compileScript_bind]
      exact compile_afterKappa_factor out gamma body z kappa kappaDraw.2

/-- Lift the compiled middle equality through the selected middle wrapper. -/
theorem compile_factoredMiddleContinuationAt_eq_middleContinuationAt
    (body : Bytes) (z : Fin 10 → K) (out : OODResult) (gamma : K)
    (digest : Block) :
    compileScript (factoredMiddleContinuationAt body z out gamma digest) =
      compileScript (middleContinuationAt body z out gamma digest) := by
  unfold factoredMiddleContinuationAt middleContinuationAt
  simp only [compileScript_bind]
  rw [compile_factoredMiddleScript_eq_middleScript]
  rfl

/-- Lift through the unchanged source/OOD/gamma prefix. -/
theorem compile_factoredPrefixMiddleScript_eq_prefixMiddleScript
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block) :
    compileScript
        (factoredPrefixMiddleScript firstWork secondWork z body digest) =
      compileScript (prefixMiddleScript firstWork secondWork z body digest) := by
  unfold factoredPrefixMiddleScript prefixMiddleScript
  simp only [compileScript_bind]
  apply congrArg (bindOracleMachine
    (compileScript
      (sourceThenGammaScript firstWork secondWork body digest)))
  funext prefixDraw
  cases prefixDraw.1 with
  | error e => rfl
  | ok pair =>
      rcases pair with ⟨out, gamma⟩
      exact compile_factoredMiddleContinuationAt_eq_middleContinuationAt
        body z out gamma prefixDraw.2

/-- Premise-free compiler equality for the complete same-body staged verifier.
The result is equality of the oracle-machine syntax produced by compilation,
not equality inferred from one interpreter or one completed trace. -/
theorem compile_factoredWholeStagedScript_eq_wholeStagedScript
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : RootCuts) (body : Bytes) (digest : Block) :
    compileScript
        (factoredWholeStagedScript firstWork secondWork z cuts body digest) =
      compileScript
        (wholeStagedScript firstWork secondWork z cuts body digest) := by
  unfold factoredWholeStagedScript wholeStagedScript
  simp only [compileScript_bind]
  rw [compile_factoredPrefixMiddleScript_eq_prefixMiddleScript]
  rfl

#print axioms compile_factoredMiddleScript_eq_middleScript
#print axioms compile_factoredMiddleContinuationAt_eq_middleContinuationAt
#print axioms compile_factoredPrefixMiddleScript_eq_prefixMiddleScript
#print axioms compile_factoredWholeStagedScript_eq_wholeStagedScript

end
end AspisV8Completion.FSV8CompiledWholeFactorization
