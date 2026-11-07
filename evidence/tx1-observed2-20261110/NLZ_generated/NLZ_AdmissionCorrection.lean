import NLZ_Resources
set_option autoImplicit false
namespace AspisR1.NLZ_AdmissionCorrection
open Aeneas Aeneas.Std AspisR1.NLZ_Resources
def empty : Heap := ⟨fun _ => none,fun _ => [],fun _ => [],fun _ => 0⟩
/-- Counterexample to the OLD unconditional-heap interface, not to the frozen
Rust. Native row packets require an admitted input-buffer interpretation. -/
theorem no_view_empty (window : Window) (bytes : List U8) : ¬ View empty window bytes := by
 intro view
 obtain ⟨o,found,_⟩ := view
 change none = some o at found
 cases found
#print axioms no_view_empty
#print no_view_empty
end AspisR1.NLZ_AdmissionCorrection
