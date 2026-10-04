import AspisV8R19.R646CombineLoopExecution
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R677C1ChunkCanonical
open Aeneas Aeneas.Std
open AspisR614SelectedCombineBeta
open AspisV8R19.R646CombineLoopExecution

lemma c1Chunk_getElem (c1 : Array U32 104#usize) (slot : Fin 4) (j : Fin 26) :
    (c1Chunk c1 slot).val[j.val] = c1.val[26*slot.val+j.val]'(by
      have h := c1.property
      have hu : (104#usize : Usize).val = 104 := by scalar_tac
      have hlen : c1.val.length = 104 := by simpa only [hu] using h
      omega) := by
  change ((c1.val.drop (26 * slot.val)).take 26)[j.val] = _
  rw [List.getElem_take]
  rw [List.getElem_drop]

/-- Any pointwise canonicality predicate on the exact 104-word C1 array
restricts to its source-shaped 26-word chunk. -/
theorem c1Chunk_pointwise (P : U32 → Prop) (c1 : Array U32 104#usize) (slot : Fin 4)
    (hfull : ∀ i : Fin 104, P c1.val[i.val]) :
    ∀ j : Fin 26, P (c1Chunk c1 slot).val[j.val] := by
  intro j
  rw [c1Chunk_getElem]
  apply hfull ⟨26*slot.val+j.val, by omega⟩

#print axioms c1Chunk_getElem
#print axioms c1Chunk_pointwise
end AspisV8R19.R677C1ChunkCanonical
