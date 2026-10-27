import XRk_DecodeModels
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
set_option autoImplicit false
namespace LPa.View
-- wide_view has no loop. Correspondence must retain offsets and borrowed fields.
-- Native inactive/borrow stage: verifier::candidate::LPa_candidate::LPa_view_inactive.
theorem inactive_reject (proof semantic y1 : Slice U8) (inactive : Slice U8)
    (slice : XRk_sliceRange proof 7495 7527 = ok inactive)
    (reject : aspis_core.field.wide_exact.WideExact.from_le_bytes inactive = ok none) :
    verifier.candidate.wide_view proof semantic y1 = ok (.Err .Parse) := by
  simp only [verifier.candidate.wide_view, slice, bind_tc_ok, reject]

theorem success (proof semantic y1 inactiveBytes round0 root round1 finalBytes : Slice U8)
    (inactive : XRk_Wide) (rootArray : Array U8 32#usize)
    (s0 : XRk_sliceRange proof 7495 7527 = ok inactiveBytes)
    (parse : aspis_core.field.wide_exact.WideExact.from_le_bytes inactiveBytes = ok (some inactive))
    (s1 : XRk_sliceRange proof 7527 7751 = ok round0)
    (s2 : XRk_sliceRange proof 7751 7783 = ok root)
    (rootLen : root.val.length = 32)
    (rootVal : rootArray.val = root.val)
    (s3 : XRk_sliceRange proof 7783 8007 = ok round1)
    (s4 : XRk_sliceRange proof 8007 10055 = ok finalBytes) :
    verifier.candidate.wide_view proof semantic y1 = ok (.Ok {
      variant := .S2, semantic := semantic, y1 := y1, inactive := inactive,
      round0 := round0, folded_root := some rootArray, round1 := round1,
      final_message := finalBytes, query_bytes := ⟨[],by decide⟩ }) := by
  have same : (⟨root.val,rootLen⟩ : Array U8 32#usize) = rootArray := by
    apply Subtype.ext
    exact rootVal.symm
  simp only [verifier.candidate.wide_view, s0, bind_tc_ok, parse, s1, s2,
    dif_pos rootLen, same, s3, s4]
#print axioms inactive_reject
#print axioms success
end LPa.View
