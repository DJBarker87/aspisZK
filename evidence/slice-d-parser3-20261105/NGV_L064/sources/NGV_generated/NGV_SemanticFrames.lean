import NGV_SemanticTrace
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_SemanticFrames
open NGV_SemanticTrace NGV_RowPayload
theorem length (input before final : Slice U8) (r : Nat) (run : Run input r before final) :
 final.val.length=before.val.length := by
 induction run with
 | done before => rfl
 | next r before live packet final rest ih => exact ih.trans (NGV_RowPayload.length packet)
/-- Earlier output bytes survive every following row, on the SAME buffer. -/
theorem prefix (input before final : Slice U8) (r : Nat) (run : Run input r before final)
 (inputSize : input.val.length=7015) :
 ∀ j,j<NGD_SemanticSchedule.dst r→final.val[j]?=before.val[j]? := by
 induction run with
 | done before => intro j _;rfl
 | next r before live packet final rest ih =>
   intro j earlier
   have mono:=NGD_SemanticSchedule.dst_mono r (r+1) (by omega) (by omega)
   exact (ih j (by omega)).trans (NGV_RowFrame.outside input before r live inputSize packet j (Or.inl earlier))
#print axioms length
#print axioms prefix
end NGV_SemanticFrames
