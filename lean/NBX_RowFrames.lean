import NBX_FrameComposition
set_option autoImplicit false
namespace NBX_RowFrames
open Aeneas Aeneas.Std Result

/-- Source-order sequence writes: one new row at each successor. The native
step's arbitrary pre-state/coordinate law supplies precisely this update. -/
def writeRows (read : Nat → U64) (start : Nat) : Nat → (Nat → U64) → (Nat → U64)
  | 0, initial => initial
  | n+1, initial => Function.update (writeRows read start n initial)
      (start+n) (read (start+n))

/-- Values inside the assigned interval come from the original byte reader;
every other row retains the arbitrary pre-state. No whole array reduction. -/
theorem value_frame (read : Nat → U64) (start count : Nat)
    (initial : Nat → U64) (i : Nat) :
    writeRows read start count initial i =
      if start ≤ i ∧ i < start+count then read i else initial i := by
  induction count with
  | zero => simp [writeRows]
  | succ n ih =>
    simp only [writeRows,Function.update_apply]
    by_cases h : i = start+n
    · subst i
      simp
    · simp only [h,if_false,ih]
      have same : (start ≤ i ∧ i < start+n) ↔ (start ≤ i ∧ i < start+(n+1)) := by omega
      simp only [same]

/-- Once every native iteration has been associated with its original read,
the result has no dependence on unread ambient rows. -/
theorem read_ext (read other : Nat → U64) (start count : Nat)
    (initial : Nat → U64)
    (same : ∀ i, start ≤ i → i < start+count → read i = other i) :
    writeRows read start count initial = writeRows other start count initial := by
  funext i
  rw [value_frame,value_frame]
  split
  · rename_i h
    exact same i h.1 h.2
  · rfl

/-- A successful fixed-width ASR8 emission changes an initially empty
runtime return-data slot. This is an effect obstruction, not an encoder law. -/
theorem nonempty_return_write (encoded : List U8) (width : encoded.length = 792) :
    encoded ≠ [] := by
  intro empty
  simp only [empty,List.length_nil] at width
  omega

#print axioms value_frame
#print axioms read_ext
#print axioms nonempty_return_write
end NBX_RowFrames
