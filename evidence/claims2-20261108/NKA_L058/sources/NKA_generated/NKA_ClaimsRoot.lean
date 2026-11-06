import NKA_ClaimsOwnership
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKA_ClaimsRoot
open Aeneas Aeneas.Std Result AspisR1PublicPreparation ClaimsUnrolledFinish
open NKA_ClaimsEffects

/-- Complete forward-instantiated claims packet. Reservation is universally
quantified, not assumed successful. All source decoder results are derived
from the SAME parsed bytes; the output retains full allocator Result/state
and, exactly on allocation success, original owned carrier and singleton size.
Native source-site interpretation is the existing Allocator/P6 item. -/
theorem claims {A : Type} (allocator : S2W_D189Wrappers.Allocator A) (state : A)
 (reservation : NP6_StdModel.Reservation) (rows : NKA_HeapCarrier.RowNative)
 (rowCut : NKA_HeapCarrier.RowCut rows) (box : NKA_HeapCarrier.BoxNative)
 (boxCut : NKA_HeapCarrier.BoxCut box) (owner : Nat)
 (before : NKA_InitializedPrefix.Memory) (bytes : Slice U8) :
 match parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
 | .ok (.Ok pre) =>
   ∃ value,NKA_ClaimsOwnership.Bound reservation rows box owner before value ∧
   native allocator state reservation rows box owner before value=
    cohort allocator state reservation (PrefixAdapter.fromOld pre) ∧
   native allocator state reservation rows box owner before value=
    reference allocator state reservation (PrefixAdapter.fromOld pre) ∧
   toMainStatus (NJT_ClaimsRef_Value.unbox (NKA_ClaimsReference.run reservation
    (fromMainPrefix (PrefixAdapter.fromOld pre))))=
    ClaimsUnrolledFinish.claims (NP6_StdModel.calls reservation) (PrefixAdapter.fromOld pre)
 | _ => True := by
 split
 · rename_i pre parser
   obtain ⟨value,first,second,third⟩:=NKA_ClaimsEffects.parsed allocator state reservation
    rows rowCut box boxCut owner before bytes pre parser
   exact ⟨value,NKA_ClaimsOwnership.bound reservation rows rowCut box boxCut owner before value,
    first,second,third⟩
 · trivial

#print axioms claims
#print claims
end AspisR1.NKA_ClaimsRoot
end
