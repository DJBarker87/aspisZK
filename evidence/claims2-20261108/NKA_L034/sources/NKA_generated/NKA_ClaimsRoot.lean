import NKA_HeapCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKA_ClaimsRoot
open Aeneas Aeneas.Std Result AspisR1PublicPreparation ClaimsUnrolledFinish
abbrev ParentClaims := AspisR1ClaimsUnrolledParent.Claims
abbrev MainClaims := NKA_HeapCarrier.Claims
abbrev MainStatus := NKA_HeapCarrier.Status

def main (value : ParentClaims) : MainClaims :=
 ⟨value.val.map toMainArray,by simpa using value.property⟩

/-- The SAME actual reserve source site, under the existing allocator item.
The request is one Claims or one MaybeUninit<Claims>:1392 bytes, alignment4.
Reservation is its observed returning outcome, universally quantified below.
The complete allocator action, including abort and returned state, is kept. -/
def allocate {A : Type} (allocator : S2W_D189Wrappers.Allocator A) (state : A) : Result A :=
 allocator.allocate state 1392

def native {A : Type} (allocator : S2W_D189Wrappers.Allocator A) (state : A)
 (reservation : NP6_StdModel.Reservation) (rows : NKA_HeapCarrier.RowNative)
 (box : NKA_HeapCarrier.BoxNative) (before : NKA_InitializedPrefix.Memory)
 (value : ParentClaims) : Result (MainStatus×A) := do
 let post ← allocate allocator state
 let result ← NKA_HeapCarrier.result reservation rows box before (main value)
 ok (result,post)

def cohort {A : Type} (allocator : S2W_D189Wrappers.Allocator A) (state : A)
 (reservation : NP6_StdModel.Reservation) (pre : MainPrefix) : Result (MainStatus×A) := do
 let post ← allocate allocator state
 let result ← claims (NP6_StdModel.calls reservation) pre
 ok (result,post)

/-- The emitted safe reference decodes as values before allocating. This
keeps that original source order and the same full allocator action. -/
def reference {A : Type} (allocator : S2W_D189Wrappers.Allocator A) (state : A)
 (reservation : NP6_StdModel.Reservation) (pre : MainPrefix) : Result (MainStatus×A) := do
 let pure ← NJT_ClaimsRef_Value.unbox
  (NJT_ClaimsRef.r1_semantic.NJT_claims_ref (fromMainPrefix pre))
 match pure with
 | .Err e => ok (.Err (toMainError e),state)
 | .Ok value => do
  let post ← allocate allocator state
  let result ← toMainStatus (NKA_ClaimsModel.reserveResult reservation value)
  ok (result,post)

theorem outcome (reservation : NP6_StdModel.Reservation) (rows : NKA_HeapCarrier.RowNative)
 (rowCut : NKA_HeapCarrier.RowCut rows) (box : NKA_HeapCarrier.BoxNative)
 (boxCut : NKA_HeapCarrier.BoxCut box) (before : NKA_InitializedPrefix.Memory) (value : ParentClaims) :
 NKA_HeapCarrier.result reservation rows box before (main value)=
 toMainStatus (NKA_ClaimsModel.reserveResult reservation value) := by
 rw [NKA_HeapCarrier.source reservation rows rowCut box boxCut]
 cases reservation <;> rfl

/-- Full Result and allocator-post-state equality. No successful reserve,
decoder, heap initialization, chosen child reply or Std dictionary premise.
The native cuts are forward-instantiated at the SAME decoded value. -/
theorem parsed {A : Type} (allocator : S2W_D189Wrappers.Allocator A) (state : A)
 (reservation : NP6_StdModel.Reservation) (rows : NKA_HeapCarrier.RowNative)
 (rowCut : NKA_HeapCarrier.RowCut rows) (box : NKA_HeapCarrier.BoxNative)
 (boxCut : NKA_HeapCarrier.BoxCut box) (before : NKA_InitializedPrefix.Memory)
 (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parser : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre)) :
 ∃ value,
 native allocator state reservation rows box before value=
  cohort allocator state reservation (PrefixAdapter.fromOld pre) ∧
 native allocator state reservation rows box before value=
  reference allocator state reservation (PrefixAdapter.fromOld pre) ∧
 toMainStatus (NJT_ClaimsRef_Value.unbox (NKA_ClaimsReference.run reservation
   (fromMainPrefix (PrefixAdapter.fromOld pre))))=
  claims (NP6_StdModel.calls reservation) (PrefixAdapter.fromOld pre) := by
 obtain ⟨value,pure,model⟩:=NKA_ClaimsModel.parsed reservation bytes pre parser
 obtain ⟨other,ref,otherModel⟩:=NKA_ClaimsReference.parsed reservation bytes pre parser
 have unboxed : NJT_ClaimsRef_Value.unbox (NKA_ClaimsReference.run reservation
   (fromMainPrefix (PrefixAdapter.fromOld pre)))=
  AspisR1ClaimsUnrolledParent.candidate_claims.claims (NKA_Reservation.external reservation)
   (fromMainPrefix (PrefixAdapter.fromOld pre)) := ref.trans otherModel.symm
 have cohortValue : claims (NP6_StdModel.calls reservation) (PrefixAdapter.fromOld pre)=
  toMainStatus (NKA_ClaimsModel.reserveResult reservation value) := congrArg toMainStatus model
 refine ⟨value,?_,?_,congrArg toMainStatus unboxed⟩
 · simp only [native,cohort,cohortValue,outcome reservation rows rowCut box boxCut]
 · simp only [native,reference,pure,bind_tc_ok,outcome reservation rows rowCut box boxCut]

/-- Private claims invocation: parser failure is non-entry. Reservation is
universally quantified with no success premise, as required by(az)(2). -/
theorem claims {A : Type} (allocator : S2W_D189Wrappers.Allocator A) (state : A)
 (reservation : NP6_StdModel.Reservation) (rows : NKA_HeapCarrier.RowNative)
 (rowCut : NKA_HeapCarrier.RowCut rows) (box : NKA_HeapCarrier.BoxNative)
 (boxCut : NKA_HeapCarrier.BoxCut box) (before : NKA_InitializedPrefix.Memory) (bytes : Slice U8) :
 match parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
 | .ok (.Ok pre) =>
   ∃ value,native allocator state reservation rows box before value=
    cohort allocator state reservation (PrefixAdapter.fromOld pre) ∧
   native allocator state reservation rows box before value=
    reference allocator state reservation (PrefixAdapter.fromOld pre) ∧
   toMainStatus (NJT_ClaimsRef_Value.unbox (NKA_ClaimsReference.run reservation
    (fromMainPrefix (PrefixAdapter.fromOld pre))))=
    claims (NP6_StdModel.calls reservation) (PrefixAdapter.fromOld pre)
 | _ => True := by
 split
 · rename_i pre parser
   exact NKA_ClaimsRoot.parsed allocator state reservation rows rowCut box boxCut before bytes pre parser
 · trivial

#print axioms outcome
#print axioms parsed
#print axioms claims
#print claims
end AspisR1.NKA_ClaimsRoot
end
