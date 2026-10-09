import FSLiveSemanticPrefix
import SourceTerminalProjection

/-!
# Same-body input to the selected semantic terminal

This leaf constructs every field-level argument passed by
`performance_verifier::semantic` to `payment_terminal` after a successful
live semantic prefix.  The 84 claims are projected from the same parsed body
as the compact-round messages and both roots.

There is currently no literal Lean definition of
`evaluate_pool_v1_pair_forest_*_selected_masked_terminal_compiled_tag73_v1`
which consumes these 84 claims and the public/context objects.  Consequently
this leaf deliberately does not take a callback, an acceptance predicate, or
the terminal equality as a premise.  The missing deterministic interface is
exactly the source evaluator on `Input.claims` and `Input.z` whose result Rust
compares with `Input.carried`.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSLiveSemanticTerminalInput

open FSOracleExecution FSBoundedTranscript
open FSLiveSemanticPrefix SameBodySemanticWire
open SemanticWireExecution SourceTerminalProjection

abbrev Bytes := List UInt8
abbrev K := FSLiveSemanticPrefix.K

noncomputable section

def word (wire : SameBodySemanticWire.Wire) : Word K :=
  fun i => wire.values.getD i.val 0

/-- Literal field arguments assembled immediately before the selected Rust
terminal call. Public payment/context values remain separate inputs to that
call and are not manufactured from the proof body. -/
structure Input where
  claims : Fin 3 -> Fin 28 -> K
  z : Fin 10 -> K
  lambda : K
  chi : K
  theta : K
  zc : Fin 10 -> K
  mu : K
  eta : K
  carried : K

def ofRun (wire : SameBodySemanticWire.Wire)
    (success : FSLiveSemanticPrefix.Success) : Input where
  claims := sourceTerminalClaims (word wire)
  z := success.z
  lambda := success.lambda
  chi := success.chi
  theta := success.theta
  zc := success.zc
  mu := success.mu
  eta := success.eta
  carried := success.finalClaim

/-- The actual 84-element Rust projection is exactly the existing decoded
fixed-field terminal projection. This proves indexing and same-body origin;
it asserts no semantic validity. -/
theorem ofRun_claims_eq_terminalProjection (wire : SameBodySemanticWire.Wire)
    (success : FSLiveSemanticPrefix.Success) :
    (ofRun wire success).claims =
      AspisV6AcceptedPathObligations.terminalProjection
        (AspisV6AcceptedPathObligations.decodedFixedFieldView
          (fixedPrefix (word wire))).pointClaim := by
  exact sourceTerminalClaims_eq_terminalProjection (word wire)

/-- Success of the live semantic prefix constructs one terminal input from
the same parsed body. No stale field table or independent roots occur in the
statement. -/
theorem successful_run_constructs_terminal_input
    (positiveTransfer : Bool) (binding : Binding) (body : Bytes)
    (tape : Tape) (oracle : Oracle) (success : FSLiveSemanticPrefix.Success)
    (accepted :
      (run tape (semanticScript positiveTransfer binding body) oracle).1 =
        some (.ok success)) :
    exists wire input,
      SameBodySemanticWire.parse body = some wire /\
      input = ofRun wire success /\
      input.claims =
        AspisV6AcceptedPathObligations.terminalProjection
          (AspisV6AcceptedPathObligations.decodedFixedFieldView
            (fixedPrefix (word wire))).pointClaim /\
      input.z = success.z /\
      input.carried = success.finalClaim := by
  obtain ⟨wire, parsed, _fields⟩ := successful_run_has_same_body_wire
    positiveTransfer binding body tape oracle success accepted
  refine ⟨wire, ofRun wire success, parsed, rfl, ?_, rfl, rfl⟩
  exact ofRun_claims_eq_terminalProjection wire success

#print axioms ofRun_claims_eq_terminalProjection
#print axioms successful_run_constructs_terminal_input

end
end AspisV8Completion.FSLiveSemanticTerminalInput
