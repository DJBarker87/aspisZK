import SelectedTerminalClaimMapping
import SelectedSemanticPackedBoundary

/-!
# Same-body positive-transfer terminal delta

This is the deterministic `positive_transfer::terminal_delta` part of the
selected research verifier.  It deliberately has no terminal callback,
terminal-acceptance, or recovery-table premise: all of its inputs are taken
from `FSLiveSemanticTerminalInput.Input`, which in turn is constructed from
the one parsed proof body and the live semantic transcript.

The surrounding pair-forest selected masked terminal remains a separate
literal-source refinement obligation.  This leaf closes the opt-in wrapper
which adds its lane-94 correction after that call, so that refinement cannot
silently leave the correction as a caller-supplied scalar.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.SelectedPositiveTerminalDeltaSource

open FSLiveSemanticPrefix SameBodySemanticWire SemanticWireExecution
open FSLiveSemanticTerminalInput SelectedTerminalClaimMapping
open AspisV8.PositiveTerminalInsertion

abbrev K := FSLiveSemanticTerminalInput.K

noncomputable section

/-- The source's `((ROW >> (9-j)) & 1)` selector bit at the reserved
positive-transfer row 1014.  This is kept as a direct finite arithmetic
definition instead of reusing a witness-side selector. -/
def row1014Bit (coordinate : Fin 10) : Bool :=
  ((1014 / 2 ^ (9 - coordinate.val)) % 2) = 1

/-- `positive_transfer::selector`, in the source's coordinate order. -/
def selector (input : Input) : K :=
  (List.ofFn fun coordinate : Fin 10 =>
    if row1014Bit coordinate then input.z coordinate else 1 - input.z coordinate).prod

/-- `positive_transfer::residual`.  The three fields are the current amount,
successor amount, and current inverse in the literal `3 x 28` claim array. -/
def residual (input : Input) : K :=
  c1 input 0 1 * c1 input 1 1 * c1 input 0 3 - 1

/-- The exact lane-94 contribution before the outer equality and eta factors.
`prepared27_eq` proves that this source-shaped square chain is `theta^27`.
-/
def compositionDelta (input : Input) : K :=
  prepared27 input.theta *
    literalPack ![0, 0, selector input * residual input, 0]

/-- The value added by the selected `v8_positive_transfer` wrapper. -/
def terminalDelta (input : Input) : K :=
  input.eta * (equalityValue input.z input.zc * compositionDelta input)

/-- Pure wrapper behaviour after the ordinary selected masked-terminal call.
The `original` argument is the result of that call; it is not assumed correct
or accepted. -/
def addDelta (original : K) (input : Input) : K := original + terminalDelta input

theorem compositionDelta_eq_power27 (input : Input) :
    compositionDelta input = input.theta ^ 27 *
      literalPack ![0, 0, selector input * residual input, 0] := by
  unfold compositionDelta
  rw [prepared27_eq]

theorem terminalDelta_eq_source_assembly (input : Input) :
    terminalDelta input = input.eta *
      (equalityValue input.z input.zc *
        (input.theta ^ 27 *
          literalPack ![0, 0, selector input * residual input, 0])) := by
  rw [terminalDelta, compositionDelta_eq_power27]

/-- The wrapper is a deterministic add after the selected terminal call. -/
theorem addDelta_eq_source (original : K) (input : Input) :
    addDelta original input = original + input.eta *
      (equalityValue input.z input.zc *
        (input.theta ^ 27 *
          literalPack ![0, 0, selector input * residual input, 0])) := by
  rw [addDelta, terminalDelta_eq_source_assembly]

/-- The correction's three semantic values are all fixed-field values from
the parsed submitted body.  These are the literal source offsets after the
one omitted D column per point row. -/
theorem ofRun_residual_body_slots (wire : SameBodySemanticWire.Wire)
    (success : FSLiveSemanticPrefix.Success) :
    residual (ofRun wire success) =
      wire.values.getD 272 0 * wire.values.getD 301 0 *
        wire.values.getD 274 0 - 1 := by
  have h01 := ofRun_claim_at_body_slot wire success 0 (⟨1, by decide⟩ : Fin 28)
  have h11 := ofRun_claim_at_body_slot wire success 1 (⟨1, by decide⟩ : Fin 28)
  have h03 := ofRun_claim_at_body_slot wire success 0 (⟨3, by decide⟩ : Fin 28)
  have e01 : c1 (ofRun wire success) 0 1 = wire.values.getD 272 0 := by
    simpa [c1] using h01
  have e11 : c1 (ofRun wire success) 1 1 = wire.values.getD 301 0 := by
    simpa [c1] using h11
  have e03 : c1 (ofRun wire success) 0 3 = wire.values.getD 274 0 := by
    simpa [c1] using h03
  unfold residual
  rw [e01, e11, e03]

/-- Same-body semantic success produces the complete positive correction
input, including every claimed field and every live transcript challenge.  No
claim is made that the enclosing pair-forest terminal accepted. -/
theorem successful_run_constructs_positive_delta_input
    (positiveTransfer : Bool) (binding : Binding) (body : List UInt8)
    (tape : FSBoundedTranscript.Tape) (oracle : FSBoundedTranscript.Oracle)
    (success : FSLiveSemanticPrefix.Success)
    (accepted :
      (FSOracleExecution.run tape
        (FSLiveSemanticPrefix.semanticScript positiveTransfer binding body) oracle).1 =
        some (.ok success)) :
    exists wire input,
      SameBodySemanticWire.parse body = some wire /\
      input = ofRun wire success /\
      residual input =
        wire.values.getD 272 0 * wire.values.getD 301 0 *
          wire.values.getD 274 0 - 1 /\
      input.z = success.z /\
      input.theta = success.theta /\
      input.zc = success.zc /\
      input.eta = success.eta := by
  obtain ⟨wire, input, parsed, inputEq, _claims, zEq, _carried⟩ :=
    successful_run_constructs_terminal_input
      positiveTransfer binding body tape oracle success accepted
  refine ⟨wire, input, parsed, inputEq, ?_, zEq, ?_, ?_, ?_⟩
  · subst input
    exact ofRun_residual_body_slots wire success
  · subst input
    rfl
  · subst input
    rfl
  · subst input
    rfl

#print axioms compositionDelta_eq_power27
#print axioms terminalDelta_eq_source_assembly
#print axioms addDelta_eq_source
#print axioms ofRun_residual_body_slots
#print axioms successful_run_constructs_positive_delta_input

end
end AspisV8Completion.SelectedPositiveTerminalDeltaSource
