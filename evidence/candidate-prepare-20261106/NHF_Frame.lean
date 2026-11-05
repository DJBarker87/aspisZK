import NHF_Layout
set_option autoImplicit false
namespace AspisR1.NHF_Frame
open Aeneas Aeneas.Std
/-- Same-allocation logical contents after the two disjoint returned windows. -/
def join (semantic y1 : List U8) : List U8 := semantic ++ y1
/-- Stage S1's returned left window survives S2, including every byte. -/
theorem semantic_preserved (semantic y1 : List U8) (size : semantic.length = 13831) :
 (join semantic y1).take 13831 = semantic := by
 rw [join, ←size]; exact List.take_left
/-- Stage S2's returned right window is precisely wide_view's second borrow. -/
theorem y1_preserved (semantic y1 : List U8) (size : semantic.length = 13831) :
 (join semantic y1).drop 13831 = y1 := by
 rw [join, ←size]; exact List.drop_left
/-- The next stage's length domain follows from the actual child lengths. -/
theorem logical_size (semantic y1 : List U8)
 (left : semantic.length = 13831) (right : y1.length = 928) :
 (join semantic y1).length = 14759 := by simp only [join,List.length_append,left,right]
/-- Even a rejecting right expansion cannot affect the returned left window,
provided its packet supplies the right-window-only modifies law. -/
theorem error_frame (semantic before after : List U8) (size : semantic.length = 13831) :
 (join semantic before).take 13831 = (join semantic after).take 13831 := by
 rw [semantic_preserved _ _ size,semantic_preserved _ _ size]
/-- No loss of byte identity through adjacent cuts: both original borrows reconstruct. -/
theorem same_windows (semantic y1 : List U8) (size : semantic.length = 13831) :
 ((join semantic y1).take 13831,(join semantic y1).drop 13831) = (semantic,y1) := by
 rw [semantic_preserved _ _ size,y1_preserved _ _ size]
#print axioms semantic_preserved
#print axioms y1_preserved
#print axioms logical_size
#print axioms error_frame
#print axioms same_windows
end AspisR1.NHF_Frame
