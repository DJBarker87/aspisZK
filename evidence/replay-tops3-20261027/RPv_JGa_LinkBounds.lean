import RPv_JGa_LinkChunk00
import RPv_JGa_LinkChunk01
import RPv_JGa_LinkChunk02
import RPv_JGa_LinkChunk03
import RPv_JGa_LinkChunk04
import RPv_JGa_LinkChunk05
import RPv_JGa_LinkChunk06
import RPv_JGa_LinkChunk07
set_option autoImplicit false
namespace AspisR1.JGa_LinkBounds
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
abbrev Good := JGa_LinkShape.Good
abbrev Endpoint := JGa_LinkShape.Endpoint
theorem layout : constants.COPY_LINKS.val= JGa_LinkChunk00.values ++ JGa_LinkChunk01.values ++ JGa_LinkChunk02.values ++ JGa_LinkChunk03.values ++ JGa_LinkChunk04.values ++ JGa_LinkChunk05.values ++ JGa_LinkChunk06.values ++ JGa_LinkChunk07.values := by
  unfold constants.COPY_LINKS
  rfl
#print axioms layout
theorem all : ∀ l∈constants.COPY_LINKS.val,Good l := by
  rw [layout]
  intro l hl
  simp only [List.mem_append,or_assoc] at hl
  rcases hl with h|h|h|h|h|h|h|h
  · exact JGa_LinkChunk00.all l h
  · exact JGa_LinkChunk01.all l h
  · exact JGa_LinkChunk02.all l h
  · exact JGa_LinkChunk03.all l h
  · exact JGa_LinkChunk04.all l h
  · exact JGa_LinkChunk05.all l h
  · exact JGa_LinkChunk06.all l h
  · exact JGa_LinkChunk07.all l h
#print axioms all
end AspisR1.JGa_LinkBounds
