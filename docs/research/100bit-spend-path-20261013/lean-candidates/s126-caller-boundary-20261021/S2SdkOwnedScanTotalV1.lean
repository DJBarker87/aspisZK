import S2SdkOwnedModelV1
import S2OwnedCheckpointScanTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ScanTotal

/-- Complete emitted function identity, at arbitrary Vec contents/length;
no concrete traversal or fixed-size normalization is performed. -/
theorem scan_eq (bytes : alloc.vec.Vec U8) :
    SdkReference.owned_checkpoint_nonzero bytes =
      AspisS2OwnedStage1.owned_checkpoint_nonzero bytes := rfl

theorem total (bytes : alloc.vec.Vec U8) :
    ∃ out : Bool, SdkReference.owned_checkpoint_nonzero bytes = ok out ∧
      (out=false ↔ ∀ j, j<bytes.val.length →
        S2OwnedCheckpointScanTotalV1.ZeroAt bytes j) := by
  rw [scan_eq]
  exact S2OwnedCheckpointScanTotalV1.scan_total bytes

theorem release_none (sdk : OwnedSdk) :
    owned_release_guards sdk {checkpoint:=none,«public»:=none,proof:=none}=ok sdk := rfl

#print core.convert.Infallible

theorem infallible_empty (x : core.convert.Infallible) : False := by cases x

#print axioms infallible_empty
#print axioms scan_eq
#print axioms total
#print axioms release_none
end AspisS2OwnedStage1.SdkReference.ScanTotal
