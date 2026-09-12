import SemanticWireExecution
import AspisFormal.V6AcceptedPathObligations

/-! Literal source indexing for the selected callback's 84 point claims.

The Rust extraction enumerates `i = 0..83` and reads
`word[271 + (i / 28) * 29 + i % 28]`.  Reshaping `i` as three rows of 28
columns gives exactly `terminalProjection` of the decoded `3 × 29` point-claim
table.  This is only an indexing/projection fact: it assumes neither callback
correctness nor semantic validity.
-/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.SourceTerminalProjection
open AspisV6TranscriptRelationGrammar
open AspisV6AcceptedPathObligations
open AspisV8Completion.SemanticWireExecution

universe u
variable {K : Type u}

/-- The fixed-field decoder consumes the first 641 entries of the 697-field
same-body word. -/
def fixedPrefix (word : Word K) : Fin 641 → K :=
  fun index => word ⟨index.val, by omega⟩

/-- Row-major flattening used by Rust's `[K; 84]` callback argument. -/
def flatTerminalSlot (row : Fin 3) (column : Fin 28) : Fin 84 :=
  ⟨row.val * 28 + column.val, by omega⟩

@[simp] theorem flatTerminalSlot_div (row : Fin 3) (column : Fin 28) :
    (flatTerminalSlot row column).val / 28 = row.val := by
  simp only [flatTerminalSlot]
  omega

@[simp] theorem flatTerminalSlot_mod (row : Fin 3) (column : Fin 28) :
    (flatTerminalSlot row column).val % 28 = column.val := by
  simp only [flatTerminalSlot]
  omega

/-- After row-major unflattening, the literal source read has the frozen
`271 + row * 29 + column` point-claim index. -/
theorem pointIndex_flatTerminalSlot (row : Fin 3) (column : Fin 28) :
    pointIndex (flatTerminalSlot row column) =
      ⟨271 + row.val * 29 + column.val, by omega⟩ := by
  apply Fin.ext
  simp [pointIndex]

/-- The 84-element source array viewed in the callback's `3 × 28` shape. -/
def sourceTerminalClaims (word : Word K) : Fin 3 → Fin 28 → K :=
  fun row column => pointClaims word (flatTerminalSlot row column)

theorem sourceTerminalClaims_apply (word : Word K)
    (row : Fin 3) (column : Fin 28) :
    sourceTerminalClaims word row column =
      word ⟨271 + row.val * 29 + column.val, by omega⟩ := by
  unfold sourceTerminalClaims pointClaims
  rw [pointIndex_flatTerminalSlot]

/-- Exact deterministic bridge from the literal 84 source reads to the
callback projection of the decoded 87 point claims. -/
theorem sourceTerminalClaims_eq_terminalProjection (word : Word K) :
    sourceTerminalClaims word =
      terminalProjection (decodedFixedFieldView (fixedPrefix word)).pointClaim := by
  funext row column
  rw [sourceTerminalClaims_apply]
  rfl

#print axioms flatTerminalSlot_div
#print axioms flatTerminalSlot_mod
#print axioms pointIndex_flatTerminalSlot
#print axioms sourceTerminalClaims_apply
#print axioms sourceTerminalClaims_eq_terminalProjection
end AspisV8Completion.SourceTerminalProjection
