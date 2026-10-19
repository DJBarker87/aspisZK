import R1SpendBaseDescent
import R1OutputNotes
import R1InputPair

/-! Build the explicit spend-witness record from the existing trace selectors.
The record construction is noncomputable because `tracePath` already is.
This file proves only that the selected field coordinates are in the base;
it does not prove spend validity from trace gates. -/
set_option autoImplicit false

namespace AspisR1.TraceSpendWitness

open R0P AspisWideTower AspisV8R15.ExactTowerBase
open AspisR1.SpendRelation AspisR1.SpendBaseDescent

abbrev E := WideExact
abbrev F := ExactBaseProjection.embed.fieldRange

private theorem baseChunk (A : Trace E) (hA : BaseTyped F A)
    (block : Fin 57) (i : Fin 8) : (OutputNotes.chunk A block) i ∈ F := by
  unfold OutputNotes.chunk digestOf poseidonState
  have hi : i.val < 8 := i.isLt
  have hc : (⟨i.val, by omega⟩ : Fin 29).val < 26 := by
    change i.val < 26
    omega
  exact hA ⟨i.val, by omega⟩ hc (poseidonBlockRow block 12)

private theorem baseSalt (A : Trace E) (hA : BaseTyped F A)
    (middle last : Fin 57) (i : Fin 8) : (OutputNotes.salt A middle last) i ∈ F := by
  unfold OutputNotes.salt
  split_ifs with hi
  · exact baseChunk A hA middle ⟨i.val + 2, by omega⟩
  · exact baseChunk A hA last ⟨i.val - 6, by omega⟩

/-- The trace-selected spend witness, using the same literal coordinates as
`SpendRelationExtraction.of_production`. -/
noncomputable def fromTrace (A : Trace E) (v0 v1 v2 : Fin (2^30)) : Witness E :=
  { inputValue := v0
    outputValue := v1
    changeValue := v2
    sk := traceSk A
    salt := traceSalt A
    path := tracePath A
    pair := InputPair.leaf A
    recipientOwner := OutputNotes.chunk A 27
    recipientSalt := OutputNotes.salt A 28 29
    changeOwner := OutputNotes.chunk A 30
    changeSalt := OutputNotes.salt A 31 32 }

/-- Every field coordinate selected by `fromTrace` comes from one of the
first 26 trace columns, so `BaseTyped` suffices for all eleven witness groups. -/
theorem base_coordinates (A : Trace E) (v0 v1 v2 : Fin (2^30))
    (hA : BaseTyped F A) : BaseCoordinates (fromTrace A v0 v1 v2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi : i.val < 8 := i.isLt
    have hc : (⟨i.val, by omega⟩ : Fin 29).val < 26 := by
      change i.val < 26
      omega
    exact hA ⟨i.val, by omega⟩ hc 12
  · intro i
    change (traceSalt A i) ∈ F
    by_cases hi : i.val < 6
    · rw [traceSalt, dif_pos hi]
      have hc : (⟨i.val + 2, by omega⟩ : Fin 29).val < 26 := by
        change i.val + 2 < 26
        have hii := i.isLt
        omega
      exact hA ⟨i.val + 2, by omega⟩ hc 44
    · rw [traceSalt, dif_neg hi]
      have hc : (⟨i.val - 6, by omega⟩ : Fin 29).val < 26 := by
        change i.val - 6 < 26
        omega
      exact hA ⟨i.val - 6, by omega⟩ hc 60
  · intro level i
    unfold fromTrace tracePath
    by_cases hz : A 0 (pathBaseRow level) = 0
    · simp [hz]
      have hr : (⟨8 + i.val, by omega⟩ : Fin 29).val < 26 := by
        change 8 + i.val < 26
        have hi := i.isLt
        omega
      exact hA ⟨8 + i.val, by omega⟩ hr (succRow (pathBaseRow level))
    · simp [hz]
      have hr : (⟨i.val, by omega⟩ : Fin 29).val < 26 := by
        change i.val < 26
        have hi := i.isLt
        omega
      exact hA ⟨i.val, by omega⟩ hr (succRow (pathBaseRow level))
  · intro i
    unfold fromTrace InputPair.leaf AppendNode.left
    exact baseChunk A hA 4 i
  · unfold fromTrace InputPair.leaf
    exact hA 0 (by omega) 1017
  · intro i
    unfold fromTrace InputPair.leaf
    have hr : (⟨2 + i.val, by omega⟩ : Fin 29).val < 26 := by
      change 2 + i.val < 26
      have hi := i.isLt
      omega
    exact hA ⟨2 + i.val, by omega⟩ hr 1017
  · unfold fromTrace InputPair.leaf
    exact hA 1 (by omega) 1017
  · intro i
    unfold fromTrace
    exact baseChunk A hA 27 i
  · intro i
    unfold fromTrace
    exact baseSalt A hA 28 29 i
  · intro i
    unfold fromTrace
    exact baseChunk A hA 30 i
  · intro i
    unfold fromTrace
    exact baseSalt A hA 31 32 i

#print axioms base_coordinates

end AspisR1.TraceSpendWitness
