import AspisV8R19.R623PackedDecoderExecution
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R631DecoderChunkShape
open Aeneas.Std

/-- Full chunks in the actual library primitive have exactly the requested size. -/
theorem chunk_length {α : Type} {n : Nat} (hn : 0 < n) (l : List α) :
    ∀ c ∈ (List.toChunksExact n hn l).1, c.length = n := by
  unfold List.toChunksExact
  split
  · simp
  · rename_i h
    simp only [List.mem_cons]
    intro c hc
    rcases hc with rfl | hc
    · simp only [List.length_take]
      exact Nat.min_eq_left (by omega)
    · exact chunk_length hn (l.drop n) c hc
termination_by l.length
decreasing_by simp only [List.length_drop]; omega

/-- Exact count and remainder of the actual chunk primitive, without reducing
any concrete byte contents. -/
theorem chunk_shape {α : Type} {n : Nat} (hn : 0 < n) (l : List α) :
    (List.toChunksExact n hn l).1.length = l.length / n ∧
    (List.toChunksExact n hn l).2.length = l.length % n := by
  unfold List.toChunksExact
  split
  · rename_i h
    simp only [List.length_nil]
    rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
    exact ⟨rfl, rfl⟩
  · rename_i h
    have ih := chunk_shape hn (l.drop n)
    simp only [List.length_drop] at ih
    simp only [List.length_cons]
    constructor
    · rw [ih.1]
      omega
    · rw [ih.2]
      omega
termination_by l.length
decreasing_by simp only [List.length_drop]; omega

#print axioms chunk_length
#print axioms chunk_shape
end AspisV8R19.R631DecoderChunkShape
