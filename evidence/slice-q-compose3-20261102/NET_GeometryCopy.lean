import NET_GeometryGather
set_option autoImplicit false
namespace NET_GeometryCopy

/-- Reuse the admitted KMX loop law; do not reimplement a copy stub or
normalize a concrete buffer. Native reserve/ownership stays separate. -/
theorem five_append {T : Type} (before values : List T) (width : values.length = 5) :
    KMX_CopyMeaning.appendLoop before values = before ++ values ∧
      (KMX_CopyMeaning.appendLoop before values).length = before.length + 5 := by
  rw [KMX_CopyMeaning.append_spec]
  exact ⟨rfl,by simp only [List.length_append,width]⟩

/-- Every prior flat word is outside the five-cell write window. -/
theorem old_flat_frame {T : Type} (src dst : Nat → T) (cursor offset : Nat)
    (old : offset < 5*cursor) :
    KMX_CopyMeaning.loop src dst (5*cursor) 5 offset = dst offset := by
  exact KMX_CopyMeaning.copy_frame src dst (5*cursor) 5 offset (Or.inl old)

/-- Every selected new word comes from the SAME shifted source window. -/
theorem new_flat_window {T : Type} (src dst : Nat → T) (cursor offset : Nat)
    (inside : offset < 5) :
    KMX_CopyMeaning.loop src dst (5*cursor) 5 (5*cursor+offset) =
      src (5*cursor+offset) := by
  rw [KMX_CopyMeaning.loop_spec,if_pos]
  omega

/-- Disjoint line-buffer addresses are framed by the flat append. Pointer
validity and the natural-address realization remain physical obligations. -/
theorem disjoint_line_frame {T : Type} (src dst : Nat → T)
    (flatBase flatLength lineBase lineLength cursor offset : Nat)
    (withinFlat : 5*cursor+5 ≤ flatLength) (withinLine : offset < lineLength)
    (disjoint : flatBase+flatLength ≤ lineBase ∨ lineBase+lineLength ≤ flatBase) :
    KMX_CopyMeaning.loop src dst (flatBase+5*cursor) 5 (lineBase+offset) =
      dst (lineBase+offset) := by
  apply KMX_CopyMeaning.copy_frame
  omega

#print axioms five_append
#print axioms old_flat_frame
#print axioms new_flat_window
#print axioms disjoint_line_frame
end NET_GeometryCopy
