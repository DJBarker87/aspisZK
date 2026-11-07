import NNG_InstallBase
import NNG_EmittedContext
import NKA_ClaimsRoot
import NLU_InputDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_InstallClaims
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer inner outer_inverse inner_inverse)
open AspisR1.NMT_Transport (arr arr_inverse)
open AspisR1PublicPreparation ClaimsUnrolledFinish NKA_ClaimsEffects
abbrev OldClaims := Array (Array AspisR1PublicPreparation.aspis_core.field.QM31 29#usize) 3#usize

def raiseClaims (c : OldClaims) : NNG_Emitted.Claims := arr (arr fromT1) c
def lowerClaims (c : NNG_Emitted.Claims) : OldClaims := arr (arr toT1) c
theorem roundtrip (c : OldClaims) : lowerClaims (raiseClaims c)=c := by
 unfold lowerClaims raiseClaims
 apply arr_inverse
 intro row
 exact arr_inverse fromT1 toT1 fromT1_inverse row
#print axioms roundtrip

def claims (reservation : NP6_StdModel.Reservation) (p : NNG_verify_finish.r1_wire.Prefix) :=
 outer (inner raiseClaims fromT13) (ClaimsUnrolledFinish.claims (NP6_StdModel.calls reservation) (toT12 p))
theorem same (reservation : NP6_StdModel.Reservation) (p : NNG_verify_finish.r1_wire.Prefix) :
 outer (inner lowerClaims toT13) (claims reservation p)=
 ClaimsUnrolledFinish.claims (NP6_StdModel.calls reservation) (toT12 p) := by
 apply outer_inverse
 intro r
 exact inner_inverse raiseClaims lowerClaims fromT13 toT13 roundtrip fromT13_inverse r
#print axioms same

/-- CLOSED129 is applied at this occurrence's SAME original Prefix. Both
reservation arms and the allocator state remain universally quantified data.
RowCut/BoxCut are the unchanged reviewed native transport, not child success. -/
theorem source {A : Type} (allocator : S2W_D189Wrappers.Allocator A) (state : A)
 (reservation : NP6_StdModel.Reservation) (rows : NKA_HeapCarrier.RowNative)
 (rowCut : NKA_HeapCarrier.RowCut rows) (box : NKA_HeapCarrier.BoxNative)
 (boxCut : NKA_HeapCarrier.BoxCut box) (owner : Nat)
 (before : NKA_InitializedPrefix.Memory) (p : NNG_verify_finish.r1_wire.Prefix)
 (hd : NLU.ParsedPrefix (toT12 p)) :
 ∃ value,NKA_ClaimsOwnership.AtAllocation (allocate allocator state) reservation rows box owner before value ∧
 native allocator state reservation rows box owner before value=
  cohort allocator state reservation (toT12 p) ∧
 native allocator state reservation rows box owner before value=
  reference allocator state reservation (toT12 p) ∧
 toMainStatus (NJT_ClaimsRef_Value.unbox (NKA_ClaimsReference.run reservation (fromMainPrefix (toT12 p))))=
  outer (inner lowerClaims toT13) (claims reservation p) := by
 obtain ⟨bytes,pre,parsed,prefixEq⟩ := hd
 have closed := NKA_ClaimsRoot.claims allocator state reservation rows rowCut box boxCut owner before bytes
 rw [parsed] at closed
 obtain ⟨value,atAllocation,nativeCohort,nativeReference,referenceSource⟩ := closed
 refine ⟨value,atAllocation,?_,?_,?_⟩
 · rw [prefixEq];exact nativeCohort
 · rw [prefixEq];exact nativeReference
 · rw [same,prefixEq];exact referenceSource
#print axioms source
end AspisR1.NNG_InstallClaims
