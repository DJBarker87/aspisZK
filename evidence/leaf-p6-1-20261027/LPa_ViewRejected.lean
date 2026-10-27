import LPa_ViewFrozen
open Aeneas Aeneas.Std Result
open XRk_Release
set_option autoImplicit false
namespace LPa.View
open LPa.Slices

theorem frozen_reject (proof semantic y1 : Slice U8) (len : proof.val.length = 57607)
    (parse : aspis_core.field.wide_exact.WideExact.from_le_bytes (segment proof 7495 7527) = ok none) :
    verifier.candidate.wide_view proof semantic y1 = ok (.Err .Parse) := by
  exact inactive_reject proof semantic y1 (segment proof 7495 7527)
    (range_success _ _ _ (by omega)) parse

#print axioms frozen_reject
end LPa.View
