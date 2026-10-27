import LPt_LPl_A_Validate
import LPt_LPl_A_StageLaws
open Aeneas Aeneas.Std Result
open LPt_LPl_Kit_Release
set_option autoImplicit false
namespace LPt_LPl_A.Validate

theorem error_index_bound (bs : Slice U8) (size : bs.val.length ≤ 3712) (i : Nat) (hit : loop bs.val = some i) :
    i ≤ UScalar.cMax .Usize := by
  have h := LPt_LPl_A.firstBad_bound (bad bs.val) (bs.val.length/32) i hit
  change i ≤ 4294967295
  omega

theorem error_exact (row : U8) (bs : Slice U8) (size : bs.val.length ≤ 3712) (i : Nat) (hit : loop bs.val = some i) :
    LPt_External.r1_wire.validate_record_fields row bs =
      ok (.Err (.NonCanonical row (UScalar.ofNat i (error_index_bound bs size i hit)))) := by
  rw [shipped_leaf_model, hit]
  simp only [dif_pos (error_index_bound bs size i hit)]

theorem accepts_of_all_stages (row : U8) (bs : Slice U8)
    (valid : ∀ i, i < bs.val.length/32 → bad bs.val i = false) :
    LPt_External.r1_wire.validate_record_fields row bs = ok (.Ok ()) := by
  have absent : loop bs.val = none := (LPt_LPl_A.firstBad_none _ _).mpr valid
  rw [shipped_leaf_model, absent]

#print axioms error_index_bound
#print axioms error_exact
#print axioms accepts_of_all_stages
end LPt_LPl_A.Validate
