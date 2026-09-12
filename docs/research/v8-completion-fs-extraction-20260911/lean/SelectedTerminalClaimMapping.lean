import FSLiveSemanticTerminalInput
import SelectedSourceTerminalAssembly

/-!
# Literal selected-terminal claim mapping

This file translates the first part of
`pair_forest_semantic_terminal::composition_parts` directly.  It splits the
same-body `3 × 28` claim array into the three 16-column Poseidon openings and
the row-zero mask-only/H/G values at the exact source columns.  It also reuses
the proved V7 equality-factor algebra for the literal ten-coordinate
`equality_value` callback component.

Public payment and transition data do not participate in this projection and
remain an explicit input to the still-missing semantic/copy evaluators.  No
terminal acceptance or callback equality is assumed here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.SelectedTerminalClaimMapping

open FSLiveSemanticTerminalInput
open FSLiveSemanticPrefix SameBodySemanticWire
open SourceTerminalProjection SemanticWireExecution
open SelectedSourceTerminalAssembly

abbrev K := FSLiveSemanticTerminalInput.K

noncomputable section

def c1 (input : Input) (point : Fin 3) : Fin 16 -> K :=
  fun column => input.claims point ⟨column.val, by omega⟩

def maskOnly (input : Input) : Fin 10 -> K :=
  fun column => input.claims 0 ⟨16 + column.val, by omega⟩

def h1 (input : Input) : K := input.claims 0 26
def g (input : Input) : K := input.claims 0 27

/-- Exact source shape of `StateOnlyPoseidonOpenings`. -/
structure Openings where
  z : Fin 16 -> K
  succZ : Fin 16 -> K
  xor12Z : Fin 16 -> K

def openings (input : Input) : Openings where
  z := c1 input 0
  succZ := c1 input 1
  xor12Z := c1 input 2

@[simp] theorem openings_z (input : Input) (column : Fin 16) :
    (openings input).z column = input.claims 0 ⟨column.val, by omega⟩ := rfl

@[simp] theorem openings_succZ (input : Input) (column : Fin 16) :
    (openings input).succZ column = input.claims 1 ⟨column.val, by omega⟩ := rfl

@[simp] theorem openings_xor12Z (input : Input) (column : Fin 16) :
    (openings input).xor12Z column = input.claims 2 ⟨column.val, by omega⟩ := rfl

@[simp] theorem maskOnly_apply (input : Input) (column : Fin 10) :
    maskOnly input column = input.claims 0 ⟨16 + column.val, by omega⟩ := rfl

@[simp] theorem h1_apply (input : Input) : h1 input = input.claims 0 26 := rfl
@[simp] theorem g_apply (input : Input) : g input = input.claims 0 27 := rfl

/-- Every selected-terminal claim used above is a literal fixed-field slot of
the same parsed body.  The extra `29` stride is the source D column omitted by
the terminal's 28-column projection. -/
theorem ofRun_claim_at_body_slot (wire : SameBodySemanticWire.Wire)
    (success : FSLiveSemanticPrefix.Success) (point : Fin 3) (column : Fin 28) :
    (ofRun wire success).claims point column =
      wire.values.getD (271 + point.val * 29 + column.val) 0 := by
  exact sourceTerminalClaims_apply (word wire) point column

theorem ofRun_h1_g_body_slots (wire : SameBodySemanticWire.Wire)
    (success : FSLiveSemanticPrefix.Success) :
    h1 (ofRun wire success) = wire.values.getD 297 0 /\
      g (ofRun wire success) = wire.values.getD 298 0 := by
  constructor
  · simpa [h1] using ofRun_claim_at_body_slot wire success 0 26
  · simpa [g] using ofRun_claim_at_body_slot wire success 0 27

/-- Literal Rust factor `1-a-b+2ab`, folded over all ten coordinates. -/
def equalityValue (left right : Fin 10 -> K) : K :=
  sourceEqualityLoop left right

/-- Reuse of the exact V7/source algebra: this is the real
`pair_forest_semantic_terminal::equality_value` component, not an abstract
callback result. -/
theorem equalityValue_eq_source (input : Input) :
    equalityValue input.zc input.z =
      AspisV8.SelectedSemanticLaneAggregation.sourceEqualityValue input.zc input.z := by
  exact sourceEqualityLoop_eq_sourceEqualityValue input.zc input.z

/-- Literal helper tail of `terminal_parts` once composition and Copy-active
have been computed by their still-separate source evaluators. -/
def helperAssembly (input : Input) (composition copyActive : K) : K :=
  equalityValue input.zc input.z * composition +
    input.mu * h1 input + input.mu * input.mu * ((1-copyActive) * h1 input)

theorem helperAssembly_eq_source (input : Input) (composition copyActive : K) :
    helperAssembly input composition copyActive =
      AspisV8.SelectedSemanticLaneAggregation.sourceEqualityValue input.zc input.z * composition +
        input.mu * h1 input + input.mu ^ 2 * ((1-copyActive) * h1 input) := by
  rw [helperAssembly, equalityValue_eq_source]
  ring

#print axioms ofRun_claim_at_body_slot
#print axioms ofRun_h1_g_body_slots
#print axioms equalityValue_eq_source
#print axioms helperAssembly_eq_source

end
end AspisV8Completion.SelectedTerminalClaimMapping
