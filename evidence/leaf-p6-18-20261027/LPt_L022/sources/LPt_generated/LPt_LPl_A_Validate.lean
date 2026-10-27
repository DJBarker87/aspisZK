import LPt_LPl_Kit_FunsExternal
import LPt_LPl_A_FirstError
open Aeneas Aeneas.Std Result
open LPt_LPl_Kit_Release
set_option autoImplicit false
namespace LPt_LPl_A.Validate
-- Native stage bridge: r1_wire::LPt_LPl_A_wire::LPt_LPl_A_validate_stage (K013).
def bad (bs : List U8) (i : Nat) : Bool :=
  !(LPt_LPl_Kit_Bytes.validChunk 8 true ((bs.drop (32*i)).take 32))
def loop (bs : List U8) : Option Nat := LPt_LPl_A.firstBad (bad bs) (bs.length/32)
theorem loop_eq_model (bs : List U8) :
    loop bs = (List.range (bs.length/32)).find? (bad bs) :=
  LPt_LPl_A.firstBad_find _ _
theorem loop_eq_fold (bs : List U8) :
    loop bs = (List.range (bs.length/32)).foldl (fun found i =>
      match found with
      | some j => some j
      | none => if bad bs i then some i else none) none :=
  LPt_LPl_A.firstBad_fold _ _
theorem shipped_leaf_model (row : U8) (bs : Slice U8) :
    LPt_External.r1_wire.validate_record_fields row bs =
      match loop bs.val with
      | none => ok (.Ok ())
      | some i => dite (i ≤ UScalar.cMax .Usize)
          (fun h => ok (.Err (.NonCanonical row (UScalar.ofNat i h))))
          (fun _ => fail .panic) := by
  rw [loop_eq_model]
  rfl
#print axioms loop_eq_model
#print axioms loop_eq_fold
#print axioms shipped_leaf_model
end LPt_LPl_A.Validate
