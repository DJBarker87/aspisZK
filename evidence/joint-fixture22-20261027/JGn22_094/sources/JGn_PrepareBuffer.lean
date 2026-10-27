import JGn_CurrentPreparation
import JFw_RealExpansion
import JFw_Y1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_PrepareBuffer
open Aeneas Aeneas.Std Result
attribute [local irreducible] List.replicate

def buffer : Slice U8 := ⟨List.replicate 14759 0#u8,by
  simp only [List.length_replicate]
  scalar_tac⟩

def back (pair : Slice U8 × Slice U8) : Slice U8 :=
  if h : pair.1.length=13831 ∧ pair.2.length=928 then
    ⟨pair.1.val++pair.2.val,by
      simp only [List.length_append]
      have hl : pair.1.val.length=13831 := h.1
      have hr : pair.2.val.length=928 := h.2
      rw [hl,hr]
      scalar_tac⟩
  else buffer

theorem length : buffer.length=14759 := List.length_replicate
#print axioms length

theorem take : buffer.val.take 13831=JFw_RealExpansion.initial.val := by
  change (List.replicate 14759 (0#u8)).take 13831=List.replicate 13831 0#u8
  rw [List.take_replicate]
  rfl
#print axioms take

theorem drop : buffer.val.drop 13831=JFw_Y1.initial.val := by
  change (List.replicate 14759 (0#u8)).drop 13831=List.replicate 928 0#u8
  rw [List.drop_replicate]
#print axioms drop

theorem split : core.slice.Slice.split_at_mut buffer 13831#usize=
    ok ((JFw_RealExpansion.initial,JFw_Y1.initial),back) := by
  unfold core.slice.Slice.split_at_mut
  rw [dif_pos (by rw [length];change 13831≤14759;omega)]
  simp only [List.splitAt_eq,take,drop]
  simp only [show JFw_RealExpansion.initial.val.length=13831 from JFw_RealExpansion.initial_length,
    show JFw_Y1.initial.val.length=928 from JFw_Y1.initial_length]
  rfl
#print axioms split

theorem recombine (semantic y1 : Slice U8) (hs : semantic.length=13831) (hy : y1.length=928) :
    (back (semantic,y1)).val=semantic.val++y1.val := by
  unfold back
  rw [dif_pos ⟨hs,hy⟩]
#print axioms recombine
end AspisR1.JGn_PrepareBuffer
end
