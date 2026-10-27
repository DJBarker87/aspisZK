import LPa_Validate
import LPa_StageLaws
open Aeneas Aeneas.Std Result
open XRk_Release
set_option autoImplicit false
namespace LPa.Validate

theorem error_index_bound (bs : Slice U8) (size : bs.val.length ≤ 3712) (i : Nat) (hit : loop bs.val = some i) :
    i ≤ UScalar.cMax .Usize := by
  have h := LPa.firstBad_bound (bad bs.val) (bs.val.length/32) i hit
  change i ≤ 4294967295
  omega

theorem error_exact (row : U8) (bs : Slice U8) (size : bs.val.length ≤ 3712) (i : Nat) (hit : loop bs.val = some i) :
    r1_wire.validate_record_fields row bs =
      ok (.Err (.NonCanonical row (UScalar.ofNat i (error_index_bound bs size i hit)))) := by
  rw [shipped_leaf_model, hit]
  simp only [dif_pos (error_index_bound bs size i hit)]

theorem accepts_of_all_stages (row : U8) (bs : Slice U8)
    (valid : ∀ i, i < bs.val.length/32 → bad bs.val i = false) :
    r1_wire.validate_record_fields row bs = ok (.Ok ()) := by
  have absent : loop bs.val = none := (LPa.firstBad_none _ _).mpr valid
  rw [shipped_leaf_model, absent]

#print axioms error_index_bound
#print axioms error_exact
#print axioms accepts_of_all_stages
end LPa.Validate
