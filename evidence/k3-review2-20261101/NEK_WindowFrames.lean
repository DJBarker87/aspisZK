/-! Generic frame composition for a future NCN one-window replay.
These laws do not identify any Rust/Kani step with its mathematical model. -/
set_option autoImplicit false
namespace NEK_WindowFrames

def writeAt {α : Type} (buffer : Nat → α) (offset : Nat) (value : α) : Nat → α :=
  fun index => if index = offset then value else buffer index

theorem writeAt_selected {α : Type} (buffer : Nat → α) (offset : Nat) (value : α) :
    writeAt buffer offset value offset = value := by
  simp [writeAt]

theorem writeAt_frame {α : Type} (buffer : Nat → α) (offset index : Nat)
    (value : α) (apart : index ≠ offset) :
    writeAt buffer offset value index = buffer index := by
  simp only [writeAt, if_neg apart]

theorem disjoint_writes {α : Type} (buffer : Nat → α) (left right : Nat)
    (a b : α) (apart : left ≠ right) :
    writeAt (writeAt buffer left a) right b =
      writeAt (writeAt buffer right b) left a := by
  funext i
  by_cases hl : i = left
  · subst i
    simp [writeAt, apart]
  · by_cases hr : i = right
    · subst i
      simp [writeAt, hl]
    · simp only [writeAt, if_neg hl, if_neg hr]

theorem window_and_frame_ext {α : Type} (actual expected : Nat → α)
    (inside : Nat → Prop) [DecidablePred inside]
    (window : ∀ i, inside i → actual i = expected i)
    (frame : ∀ i, ¬ inside i → actual i = expected i) : actual = expected := by
  funext i
  by_cases h : inside i
  · exact window i h
  · exact frame i h

theorem finite_windows_ext {α : Type} (n : Nat) (actual expected : Fin n → α)
    (windows : ∀ i, actual i = expected i) : actual = expected := by
  funext i
  exact windows i

#print axioms writeAt_selected
#print axioms writeAt_frame
#print axioms disjoint_writes
#print axioms window_and_frame_ext
#print axioms finite_windows_ext
end NEK_WindowFrames
