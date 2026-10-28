import NDF_ChunkWords
set_option autoImplicit false
namespace NDF_ChunkGeometry
open Aeneas Aeneas.Std Result

theorem widths {α : Type} (n : Nat) (positive : 0<n) (bytes : List α) :
    ∀ chunk∈(List.toChunksExact n positive bytes).1,chunk.length=n := by
  unfold List.toChunksExact
  split
  · simp
  · rename_i full
    simp only [List.mem_cons]
    intro chunk member
    rcases member with rfl | member
    · simp only [List.length_take]
      omega
    · exact widths n positive (bytes.drop n) chunk member
termination_by bytes.length
decreasing_by simp only [List.length_drop];omega

theorem count {α : Type} (bytes : List α) :
    (List.toChunksExact 32 (by decide) bytes).1.length=bytes.length/32 := by
  unfold List.toChunksExact
  split
  · simp only [List.length_nil]
    omega
  · have tail := count (bytes.drop 32)
    simp only [List.length_cons,tail,List.length_drop] at *
    omega
termination_by bytes.length
decreasing_by simp only [List.length_drop];omega

theorem window {α : Type} (bytes : List α) (i : Nat) (bound : i<bytes.length/32) :
    (List.toChunksExact 32 (by decide) bytes).1[i]'(by rw [count];exact bound) =
      (bytes.drop (32*i)).take 32 := by
  induction i generalizing bytes with
  | zero =>
    have full : ¬bytes.length<32 := by omega
    rw [List.toChunksExact,if_neg full]
    simp only [List.getElem_cons_zero,Nat.mul_zero,List.drop_zero]
  | succ i ih =>
    have full : ¬bytes.length<32 := by omega
    rw [List.toChunksExact,if_neg full]
    simp only [List.getElem_cons_succ]
    rw [ih (bytes.drop 32) (by simp only [List.length_drop];omega)]
    simp only [List.drop_drop]
    congr 2
    omega

#print axioms widths
#print axioms count
#print axioms window
end NDF_ChunkGeometry
