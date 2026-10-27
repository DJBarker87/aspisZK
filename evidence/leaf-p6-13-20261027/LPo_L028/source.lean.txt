import LPo_B_LPc_DecodeSuccess
import LPo_B_LPa_BoundaryPure
open Aeneas Aeneas.Std Result LPl_Kit_Release LPl_Kit_FieldExternal
set_option autoImplicit false
namespace LPo.BC.Boundary
/-- The actual28-value decode derives every canonical operand of the fold.
The head is also the seed, matching the shipped double occurrence of p[0]. -/
theorem decoded_canonical (r : r1_wire.ValidatedRecord)
    (p : Array aspis_core.field.QM31 28#usize)
    (decoded : r1_wire.ValidatedRecord.decode_k 28#usize r 0#usize = ok (.Ok p)) :
    ∃ result, r1_semantic.semantic_boundary p = ok result ∧ LPo.BA.Add.Canonical result := by
  have all := LPo.BC.Decode.success_canonical 28#usize r 0#usize p decoded
  have bound : 0 < p.val.length := by have h := p.property; change p.val.length = 28 at h; omega
  let seed := p.val[0]'bound
  have zero : (0#usize).val = 0 := by norm_num [UScalar.ofNatCore_val_eq]
  have head : Array.index_usize p 0#usize = ok seed := by
    rw [Array.index_usize, Array.getElem?_Usize_eq, zero,
      List.getElem?_eq_getElem bound]
  refine ⟨p.val.foldl LPo.BA.Add.field seed, ?_, ?_⟩
  · rw [← LPo.BA.Boundary.loop_eq_model, LPo.BA.Boundary.loop_pure, head]
    rfl
  · exact LPo.BA.Add.fold_canonical p.val all seed (all seed (List.getElem_mem bound))
#print axioms decoded_canonical
end LPo.BC.Boundary
