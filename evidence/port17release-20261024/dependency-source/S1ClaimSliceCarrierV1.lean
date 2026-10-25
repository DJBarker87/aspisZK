import S1ClaimOwnedOuterCompleteV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.BorrowedAbiCarrier
/-- A pure view of the very same slice data, with its own derived length.
This is a logical carrier identity, not a runtime allocation or copy. -/
def asArray {A : Type} (bytes : Slice A) : Array A (Slice.len bytes) :=
  ⟨bytes.val,by simp only [Slice.len,Usize.ofNatCore_val_eq]⟩

theorem same_slice {A : Type} (bytes : Slice A) :
    Array.to_slice (asArray bytes)=bytes := by
  apply Subtype.ext
  rfl

#print axioms asArray
#print axioms same_slice
end AspisR1CurrentPreparedClaim.BorrowedAbiCarrier
