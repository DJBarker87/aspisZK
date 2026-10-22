import Lean.Elab.Tactic.Omega
set_option autoImplicit false

namespace AspisS2SdkNativeFrameCoverage

/-- Exact scalar observation used by the native Kani window harness. Fin65536
is the mathematical value domain of its u16 ghost; no SDK carrier is replaced. -/
def observedIndex (window : Fin 15) (offset : Fin 65536) : Nat :=
  4096 * window.val + offset.val % 4096

/-- Every source proof-buffer byte has a representable observation. The final
window is truncated by the same source bounds assumption as the Kani harness. -/
theorem index_covered (i : Nat) (valid : i < 58295) :
    ∃ window : Fin 15, ∃ offset : Fin 65536, observedIndex window offset = i := by
  have remainder : i % 4096 < 4096 := Nat.mod_lt i (by decide)
  let window : Fin 15 := ⟨i / 4096, by omega⟩
  let offset : Fin 65536 := ⟨i % 4096, by omega⟩
  refine ⟨window, offset, ?_⟩
  dsimp [observedIndex, window, offset]
  rw [Nat.mod_eq_of_lt remainder]
  exact Nat.div_add_mod i 4096

/-- One checked Kani ghost window, expressed on the before/after byte-list
projections. This proposition is an interface, not an SDK execution theorem. -/
def WindowFrame {α : Type} (before after : List α) (window : Fin 15) : Prop :=
  ∀ offset : Fin 65536, observedIndex window offset < 58295 →
    before[observedIndex window offset]? = after[observedIndex window offset]?

/-- Combine all fifteen checked windows without unfolding concrete byte data.
Both length facts correspond to explicit native-harness observations. -/
theorem proof_buffer_frame {α : Type} (before after : List α)
    (beforeLength : before.length = 58295) (afterLength : after.length = 58295)
    (windows : ∀ window, WindowFrame before after window) : before = after := by
  apply List.ext_getElem?
  intro i
  by_cases valid : i < 58295
  · obtain ⟨window, offset, same⟩ := index_covered i valid
    have cell := windows window offset
    rw [same] at cell
    exact cell valid
  · rw [List.getElem?_eq_none (by omega : before.length ≤ i),
      List.getElem?_eq_none (by omega : after.length ≤ i)]

/-- Full-list frame from a bounded-index observation and the explicit length
frame; used for the native public/checkpoint allocation cases. -/
theorem bounded_buffer_frame {α : Type} (before after : List α)
    (sameLength : before.length = after.length)
    (cells : ∀ i, i < before.length → before[i]? = after[i]?) : before = after := by
  apply List.ext_getElem?
  intro i
  by_cases valid : i < before.length
  · exact cells i valid
  · rw [List.getElem?_eq_none (by omega : before.length ≤ i),
      List.getElem?_eq_none (by omega : after.length ≤ i)]

/-- Mathematical composition of the actual native probe partitions. These are
byte-list projections of original allocations, never substitute SDK accounts.
The external source certificate must instantiate every premise from one
unchanged native execution; this theorem alone is not actual-source closure. -/
theorem all_buffers_frame {α : Type} (before after : Fin 3 → List α)
    (lengths : ∀ root, (before root).length = (after root).length)
    (proofLength : (before 0).length = 58295)
    (windows : ∀ window, WindowFrame (before 0) (after 0) window)
    (publicCells : ∀ i, i < (before 1).length → (before 1)[i]? = (after 1)[i]?)
    (checkpointCells : ∀ i, i < (before 2).length → (before 2)[i]? = (after 2)[i]?) :
    before = after := by
  have proof := proof_buffer_frame (before 0) (after 0) proofLength
    ((lengths 0).symm.trans proofLength) windows
  have publicFrame := bounded_buffer_frame (before 1) (after 1) (lengths 1) publicCells
  have checkpointFrame := bounded_buffer_frame (before 2) (after 2) (lengths 2) checkpointCells
  funext root
  have cases : root = 0 ∨ root = 1 ∨ root = 2 := by
    have bound := root.isLt
    have alternatives : root.val = 0 ∨ root.val = 1 ∨ root.val = 2 := by omega
    rcases alternatives with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rcases cases with rfl | rfl | rfl
  · exact proof
  · exact publicFrame
  · exact checkpointFrame

#print axioms index_covered
#print axioms proof_buffer_frame
#print axioms bounded_buffer_frame
#print axioms all_buffers_frame
end AspisS2SdkNativeFrameCoverage
