import NDO_JGn_CurrentPreparation
import NDO_JGn_SplitSource
import NDO_JFw_RealExpansion
import NDO_JFw_Y1
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
  obtain ⟨left,right,actual,run,hl,hr,hb⟩ := JGn_SplitSource.source buffer 13831#usize
    (by rw [length];change 13831≤14759;omega)
  have el : left=JFw_RealExpansion.initial := by
    apply Subtype.ext
    exact hl.trans take
  have er : right=JFw_Y1.initial := by
    apply Subtype.ext
    exact hr.trans drop
  rw [el,er,JFw_RealExpansion.initial_length,JFw_Y1.initial_length] at hb
  have same : actual=back := by
    funext pair
    apply Subtype.ext
    rw [hb]
    unfold back
    split <;> rfl
  rw [el,er,same] at run
  exact run
#print axioms split

theorem recombine (semantic y1 : Slice U8) (hs : semantic.length=13831) (hy : y1.length=928) :
    (back (semantic,y1)).val=semantic.val++y1.val := by
  unfold back
  rw [dif_pos ⟨hs,hy⟩]
#print axioms recombine
end AspisR1.JGn_PrepareBuffer
end
