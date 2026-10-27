import LPb_ListWidths
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
open LPb_CheckpointLayout LPb_ByteFold LPb_ListWidths
namespace LPb_PayloadWidth
/-- Exact S2 bound, without reducing a concrete payload or recurrence. -/
theorem payload_width (p : verifier.Prepared) (a : verifier.Accumulator)
    (ph uh : Array U8 32#usize) (ws : List (Array U8 32#usize))
    (hw : ws.length = 6) (ha : a.weights.val.length = 64) :
    (bytes p a ph uh ws).length = 1736 := by
  have hroots := array_bytes 32#usize p.roots.val
  have hinitial := array_bytes 32#usize (ws.take 4)
  have hfinal := array_bytes 32#usize (ws.drop 4)
  have hqueries := flatMap_length XRk_wordBytes 4 word_length p.queries.val
  have hsem := scalars_length p.semantic_alpha.val
  have hz : ∀ z : aspis_core.circle.SecureCirclePoint,
      (XRk_qBytes z.x ++ XRk_qBytes z.y).length = 32 := by
    intro z
    rw [List.length_append,scalar_length,scalar_length]
  have hpoints := flatMap_length (fun z : aspis_core.circle.SecureCirclePoint =>
    XRk_qBytes z.x ++ XRk_qBytes z.y) 32 hz p.z.val
  have hweights := scalars_length a.weights.val
  simp only [List.length_take,hw,List.length_drop] at hinitial hfinal
  simp only [bytes,List.length_append,List.length_cons,List.length_nil,
    ph.property,uh.property,p.state.property,hroots,p.roots.property,hinitial,
    scalar_length,hqueries,p.queries.property,hsem,p.semantic_alpha.property,
    hpoints,p.z.property,hfinal,hweights,ha]
  rfl
#print axioms payload_width
end LPb_PayloadWidth
