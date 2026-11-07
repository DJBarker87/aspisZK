import NLU_InputDomain
import NKA_ClaimsRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Claims
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NKA_ClaimsEffects
/-- Install the CLOSED129 complete allocator/owned-value packet at THIS136
input's prefix and SAME reservation. The decoded value is produced internally.
This intermediate theorem does not assume a successful allocation/decoder or
replace the enclosing native parent state/heap continuation obligation. -/
theorem source {A H : Type} (i : NLU.Input H) (domain : NLU.InputDomain i)
 (allocator : S2W_D189Wrappers.Allocator A) (state : A)
 (rows : NKA_HeapCarrier.RowNative) (rowCut : NKA_HeapCarrier.RowCut rows)
 (box : NKA_HeapCarrier.BoxNative) (boxCut : NKA_HeapCarrier.BoxCut box)
 (owner : Nat) (before : NKA_InitializedPrefix.Memory) :
 ∃ value,NKA_ClaimsOwnership.AtAllocation (allocate allocator state) i.reservation rows box owner before value ∧
 native allocator state i.reservation rows box owner before value=cohort allocator state i.reservation i.prefix1 ∧
 native allocator state i.reservation rows box owner before value=reference allocator state i.reservation i.prefix1 ∧
 toMainStatus (NJT_ClaimsRef_Value.unbox (NKA_ClaimsReference.run i.reservation
  (ClaimsUnrolledFinish.fromMainPrefix i.prefix1)))=
 ClaimsUnrolledFinish.claims (NP6_StdModel.calls i.reservation) i.prefix1 := by
 obtain ⟨bytes,pre,parsed,samePrefix⟩:=domain.parsedPrefix
 have packet:=NKA_ClaimsRoot.claims allocator state i.reservation rows rowCut box boxCut owner before bytes
 rw [parsed] at packet
 rw [samePrefix]
 exact packet
#print axioms source
set_option pp.proofs false in #print source
end AspisR1.NLU_Claims
end
