import NBS_GeometryDomains
import KMX_CopyMeaning
set_option autoImplicit false
namespace NET_GeometryAllocation

/-- Frame observations at every offset compose a single extend operation.
This is a value law; native allocation and live-place transport are separate. -/
theorem extend_from_windows {T : Type} (before after values : List T)
    (length : after.length = before.length + values.length)
    (windows : ∀ (offset : Nat) (valid : offset < after.length),
      after[offset] = if h : offset < before.length then before[offset]
      else values[offset-before.length]'(by omega)) :
    after = before ++ values := by
  apply List.ext_getElem
  · simp only [List.length_append]; exact length
  · intro offset ha hb
    rw [windows offset ha]
    by_cases inside : offset < before.length
    · simp only [dif_pos inside,List.getElem_append_left inside]
    · simp only [dif_neg inside,List.getElem_append_right (by omega : before.length ≤ offset)]

/-- Both native buffers keep their nongrowing capacity on one five-word
append and one line-word push, at the same query cursor. -/
theorem forward_invariant (count cursor flatLength lineLength : Nat)
    (bound : count ≤ 22) (active : cursor < count)
    (flat : flatLength = 5 * cursor) (line : lineLength = cursor) :
    flatLength + 5 = 5 * (cursor+1) ∧ lineLength+1 = cursor+1 ∧
    flatLength+5 ≤ 5*count ∧ lineLength+1 ≤ count ∧
    flatLength+5 ≤ 110 := by omega

/-- Exact reverse traversal bounds, including the first and final cells. -/
theorem reverse_invariant (count remaining : Nat)
    (bound : count ≤ 22) (positive : 0 < remaining) (inside : remaining ≤ 5*count) :
    remaining-1 < 5*count ∧ remaining-1 < 110 ∧
    remaining-1+1 = remaining ∧ remaining-1 < remaining := by omega

/-- A single indexed write preserves every distinct live value window. -/
theorem backward_frame {T : Type} (before : List T) (index offset : Nat) (value : T)
    (different : offset ≠ index) :
    (before.set index value)[offset]? = before[offset]? := by
  exact List.getElem?_set_ne different.symm

#print axioms extend_from_windows
#print axioms forward_invariant
#print axioms reverse_invariant
#print axioms backward_frame
end NET_GeometryAllocation
