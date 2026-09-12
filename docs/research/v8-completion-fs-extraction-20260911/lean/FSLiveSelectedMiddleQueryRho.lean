import FSLiveSourceThenGammaV7Decode
import FSLiveQueryRhoSuffix

/-!
# Selected live gamma-to-rho middle transcript

This file joins the already traced source/OOD/gamma prefix to the exact
final256/query/rho suffix through the selected structured-relation middle.
All proof-carried bytes come from the same body at their pinned offsets.

The compact public functional description and ordinary claim are computed by
the verifier after gamma and kappa in `structured_weights::prepare`; their
field/arithmetic producer is not yet represented in this Lean source model.
They therefore remain one explicit `FunctionalProducer` boundary.  This file
does not call that boundary a same-body refinement and makes no freshness or
probability claim.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSLiveSelectedMiddleQueryRho

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSNonzeroQM31 FSLiveNonzeroV7Decode
open FSV8PostOODGammaScript FSLiveSourceThenGammaV7Decode
open FSLiveQueryRhoSuffix

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Transcript := FSBoundedTranscript.Transcript
abbrev Block := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K
abbrev Point := FSV7OODBodyScript.Point
abbrev OODResult := FSV7OODBodyScript.Result

noncomputable section

/-- The only remaining deterministic source producer in this slice.  Rust
constructs both byte strings from the fixed body, OOD points, gamma, kappa,
the compiled masks and public statement.  Lean source refinement of that
construction remains open. -/
structure FunctionalProducer where
  description : OODResult -> K -> K -> Bytes
  claim : OODResult -> K -> K -> Bytes

def inactiveClaimBytes (body : Bytes) : Bytes := (body.drop 5728).take 16
def response0Bytes (body : Bytes) : Bytes := (body.drop 6672).take 96
def alpha0NonceBytes (body : Bytes) : Bytes := (body.drop 11212).take 8

def compactFunctionalProfile : Bytes :=
  [97,115,112,105,115,45,118,56,45,105,109,97,103,101,45,103,97,116,101,
   45,99,111,109,112,97,99,116,45,102,117,110,99,116,105,111,110,97,108,
   45,118,50]

inductive Error where
  | kappa (error : FSNonzeroQM31.Error)
  | tau (error : FSNonzeroQM31.Error)
  | alpha0 (error : FSNonzeroQM31.Error)
  | suffix (error : FSLiveQueryRhoSuffix.Error)
  deriving DecidableEq

structure Success where
  kappa : K
  tau : K
  alpha0 : K
  queries : List Nat
  rho : K

abbrev Result := Except Error Success

/-- Exact selected middle beginning immediately after successful gamma.
Round 0 is absorbed before alpha0; final256 is absorbed only after alpha0 by
`queryRhoScript`, and that suffix fixes the query schedule before rho. -/
def middleQueryRhoScript (producer : FunctionalProducer) (out : OODResult)
    (gamma : K) (body : Bytes) (digest : Block) :=
  bind (absorbScript digest 50 (inactiveClaimBytes body)) fun afterInactive =>
    bind (nonzeroScript 3 afterInactive) fun kappaDraw =>
      match kappaDraw.1 with
      | .error e => .done (Except.error (Error.kappa e), kappaDraw.2)
      | .ok kappa =>
        bind (absorbScript kappaDraw.2 1
            (producer.description out gamma kappa)) fun afterDescription =>
          bind (absorbScript afterDescription 6
              (producer.claim out gamma kappa)) fun afterClaim =>
            bind (absorbScript afterClaim 1 compactFunctionalProfile)
                fun afterImageProfile =>
              bind (nonzeroScript 3 afterImageProfile) fun tauDraw =>
                match tauDraw.1 with
                | .error e => .done (Except.error (Error.tau e), tauDraw.2)
                | .ok tau =>
                  bind (absorbScript tauDraw.2 52
                      (0 :: response0Bytes body)) fun afterResponse0 =>
                    bind (absorbScript afterResponse0 20
                        (0 :: alpha0NonceBytes body)) fun afterAlphaNonce =>
                      bind (candidateScript afterAlphaNonce) fun alphaDraw =>
                        match alphaDraw.1 with
                        | .error e =>
                          .done (Except.error (Error.alpha0 e), alphaDraw.2)
                        | .ok alpha0 =>
                          bind (m := 0) (queryRhoScript body alphaDraw.2)
                            fun suffixDraw =>
                              .done (match suffixDraw.1 with
                                | .error e =>
                                  (Except.error (Error.suffix e), suffixDraw.2)
                                | .ok (queries, rho) =>
                                  (Except.ok
                                    (Success.mk kappa tau alpha0 queries rho),
                                      suffixDraw.2))

/-- The full deterministic source-shaped slice.  The producer is invoked only
after a successful OOD/gamma prefix and then only after kappa is known. -/
def sourceMiddleQueryRhoScript {n m : Nat}
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (body : Bytes) (digest : Block) :=
  bind (sourceThenGammaScript firstWork secondWork body digest) fun prefixDraw =>
    match prefixDraw.1 with
    | .error _ => .abort
    | .ok (out, gamma) =>
      middleQueryRhoScript producer out gamma body prefixDraw.2

/-- Success of the composite entails success of the actual source/OOD/gamma
script and success of the literal middle/suffix from that exact final digest
and oracle.  This is the useful deterministic splice; no distribution premise
is introduced. -/
theorem successful_source_middle_components {n m : Nat}
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (body : Bytes) (digest : Block)
    (tape : Tape) (oracle : Oracle) (success : Success) (finalDigest : Block)
    (accepted :
      (run tape (sourceMiddleQueryRhoScript firstWork secondWork producer body digest)
        oracle).1 = some (.ok success, finalDigest)) :
    exists out gamma prefixDigest,
      (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).1 =
        some (.ok (out, gamma), prefixDigest) /\
      (run tape (middleQueryRhoScript producer out gamma body prefixDigest)
        (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).2).1 =
        some (.ok success, finalDigest) := by
  unfold sourceMiddleQueryRhoScript at accepted
  rw [run_bind] at accepted
  cases prefixRun :
      (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).1 with
  | none => simp [prefixRun] at accepted
  | some prefixValue =>
    rcases prefixValue with ⟨prefixResult, prefixDigest⟩
    cases prefixResult with
    | error e => simp [prefixRun, run] at accepted
    | ok pair =>
      rcases pair with ⟨out, gamma⟩
      simp only [prefixRun] at accepted
      exact ⟨out, gamma, prefixDigest, rfl, accepted⟩

/-- Literal proof-body ranges and source labels in the successful middle.
This theorem prevents offset drift independently of the open functional
producer. -/
theorem literal_body_ranges (body : Bytes) :
    inactiveClaimBytes body = (body.drop (358*16)).take 16 /\
    response0Bytes body = (body.drop (417*16)).take (6*16) /\
    alpha0NonceBytes body = (body.drop 11212).take 8 := by
  simp [inactiveClaimBytes, response0Bytes, alpha0NonceBytes]

#print axioms successful_source_middle_components
#print axioms literal_body_ranges

end
end AspisV8Completion.FSLiveSelectedMiddleQueryRho
