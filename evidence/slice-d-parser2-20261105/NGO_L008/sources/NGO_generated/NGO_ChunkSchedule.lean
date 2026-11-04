import NGD_DecodeGeometry
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_ChunkSchedule
/-- The data-independent native schedule, before any error can stop it. -/
def windows {α : Type} (bytes : List α) : Nat → List (List α)
  | 0 => []
  | n+1 => bytes.take 32 :: windows (bytes.drop 32) n

theorem exact_chunks {α : Type} (bytes : List α) (n : Nat)
    (length : bytes.length = 32*n) :
    List.toChunksExact 32 (by omega) bytes = (windows bytes n,[]) := by
  induction n generalizing bytes with
  | zero =>
    have empty : bytes=[] := List.length_eq_zero.mp (by omega)
    subst bytes
    rw [List.toChunksExact.eq_def]
    rfl
  | succ n ih =>
    rw [List.toChunksExact.eq_def]
    have enough : ¬bytes.length<32 := by omega
    rw [dif_neg enough]
    rw [ih (bytes.drop 32) (by simp only [List.length_drop];omega)]
    rfl

theorem window_count {α : Type} (bytes : List α) (n : Nat) :
    (windows bytes n).length=n := by
  induction n generalizing bytes with
  | zero => rfl
  | succ n ih => simp only [windows,List.length_cons,ih]

theorem window_at {α : Type} (bytes : List α) (n i : Nat) (live : i<n) :
    (windows bytes n)[i]'(by rw [window_count];exact live) =
      (bytes.drop (32*i)).take 32 := by
  induction n generalizing bytes i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [windows]
    | succ i =>
      simp only [windows,List.getElem_cons_succ]
      rw [ih (bytes.drop 32) i (by omega)]
      simp only [List.drop_drop]
      congr 2 <;> omega

/-- Relates original native chunks to every indexed emitted input, not just
an observed step. There are exactly N chunks, with no trailing remainder. -/
theorem original_window (payload : List U8) (off n : Nat)
    (fitting : 32*off+32*n≤payload.length) :
    let bytes := (payload.drop (32*off)).take (32*n)
    List.toChunksExact 32 (by omega) bytes = (windows bytes n,[]) ∧
    (windows bytes n).length=n ∧
    ∀ i, i<n → ((windows bytes n)[i]'(by rw [window_count];assumption)).take 16 =
      (payload.drop (32*(off+i))).take 16 := by
  dsimp
  have length : ((payload.drop (32*off)).take (32*n)).length=32*n := by
    simp only [List.length_take,List.length_drop];omega
  refine ⟨exact_chunks _ n length,window_count _ n,?_⟩
  intro i live
  rw [window_at _ n i live]
  exact NGD_DecodeGeometry.selected_low payload off n i live
#print axioms exact_chunks
#print axioms window_count
#print axioms window_at
#print axioms original_window
end NGO_ChunkSchedule
