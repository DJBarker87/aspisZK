import NLZ_Resources
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLZ_Resources
/-- Resource framing composes on the SAME intermediate heap. Support only;
the native segment must establish each premise at its actual cut. -/
theorem frame_refl (allowed : List Nat) (h : Heap) : Frame allowed h h := by
 exact ⟨fun _ _ => rfl,rfl,rfl,rfl⟩
theorem frame_trans (left right : List Nat) (a b c : Heap)
 (first : Frame left a b) (second : Frame right b c) :
 Frame (left ++ right) a c := by
 rcases first with ⟨f,fe,fm,fb⟩
 rcases second with ⟨g,ge,gm,gb⟩
 refine ⟨?_,ge.trans fe,gm.trans fm,gb.trans fb⟩
 intro id outside
 have l : id ∉ left := fun inside => outside (List.mem_append_left right inside)
 have r : id ∉ right := fun inside => outside (List.mem_append_right left inside)
 exact (g id r).trans (f id l)
theorem view_frame (allowed : List Nat) (a b : Heap) (w : Window)
 (bytes : List Aeneas.Std.U8)
 (frame : Frame allowed a b) (outside : w.allocation ∉ allowed)
 (view : View a w bytes) : View b w bytes := by
 obtain ⟨o,found,rest⟩ := view
 exact ⟨o,(frame.1 w.allocation outside).trans found,rest⟩
#print axioms frame_refl
#print axioms frame_trans
#print axioms view_frame
end AspisR1.NLZ_Resources
end
