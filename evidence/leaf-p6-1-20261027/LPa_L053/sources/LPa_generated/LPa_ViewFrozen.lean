import LPa_View
import LPa_Slices
open Aeneas Aeneas.Std Result
open XRk_Release
set_option autoImplicit false
namespace LPa.View
open LPa.Slices

def root (proof : Slice U8) (len : proof.val.length = 57607) : Array U8 32#usize :=
  ⟨(segment proof 7751 7783).val,by
    have h : 7751 ≤ 7783 ∧ 7783 ≤ proof.val.length := by omega
    have size := segment_length proof 7751 7783 h
    exact size⟩

theorem frozen_success (proof semantic y1 : Slice U8) (len : proof.val.length = 57607)
    (inactive : XRk_Wide)
    (parse : aspis_core.field.wide_exact.WideExact.from_le_bytes (segment proof 7495 7527) = ok (some inactive)) :
    verifier.candidate.wide_view proof semantic y1 = ok (.Ok {
      variant := .S2, semantic := semantic, y1 := y1, inactive := inactive,
      round0 := segment proof 7527 7751, folded_root := some (root proof len),
      round1 := segment proof 7783 8007, final_message := segment proof 8007 10055,
      query_bytes := ⟨[],by decide⟩ }) := by
  apply success proof semantic y1 (segment proof 7495 7527)
    (segment proof 7527 7751) (segment proof 7751 7783)
    (segment proof 7783 8007) (segment proof 8007 10055) inactive (root proof len)
  · exact range_success _ _ _ (by omega)
  · exact parse
  · exact range_success _ _ _ (by omega)
  · exact range_success _ _ _ (by omega)
  · exact segment_length _ _ _ (by omega)
  · rfl
  · exact range_success _ _ _ (by omega)
  · exact range_success _ _ _ (by omega)

#print axioms frozen_success
end LPa.View
