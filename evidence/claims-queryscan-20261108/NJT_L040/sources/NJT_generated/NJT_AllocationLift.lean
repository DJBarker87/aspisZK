import NJT_ClaimsRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJT_AllocationLift
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open ClaimsUnrolledFinish

/-- Full allocator Result and returned allocator state; no success bit or
arbitrary operation dictionary replaces the headline's allocator action. -/
def before {A B : Type} (allocation : Result A) (pure : Result B) : Result (B×A) := do
 let post ← allocation
 let value ← pure
 ok (value,post)
def after {A B : Type} (allocation : Result A) (pure : Result B) : Result (B×A) := do
 let value ← pure
 let post ← allocation
 ok (value,post)

theorem commute {A B : Type} (allocation : Result A) (value : B) :
 before allocation (ok value)=after allocation (ok value) := by
 cases allocation <;> rfl

/-- The entered reference has no decoder rejection/abort before allocation.
This does not assert that the actual allocator returns successfully. -/
theorem pure_success (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre)) :
 ∃ value,NJT_ClaimsRef_Value.unbox (NJT_ClaimsRef.r1_semantic.NJT_claims_ref
  (fromMainPrefix (PrefixAdapter.fromOld pre)))=ok (.Ok value) := by
 obtain ⟨record,getter,row,decoded⟩:=NJT_QClaimsCanonical.claims bytes pre parsed
 let low : AspisR1ClaimsUnrolledParent.Record := ⟨record.row,record.framed⟩
 have called : sourceRecord (fromMainPrefix (PrefixAdapter.fromOld pre)) 25#u8=ok (.Ok low) := by
  unfold sourceRecord
  rw [prefix_back,getter]
  rfl
 obtain ⟨a,da⟩:=decoded 0#usize 0#usize (by decide) (by rfl)
 obtain ⟨b,db⟩:=decoded 1#usize 29#usize (by decide) (by rfl)
 obtain ⟨c,dc⟩:=decoded 2#usize 58#usize (by decide) (by rfl)
 have la : sourceDecode 29#usize low 0#usize=ok (.Ok (fromMainArray a)) := by
  unfold sourceDecode
  change (match AspisS1ExtractedRoundChildren.decodeMain 29#usize record 0#usize with
   | .ok (.Ok x) => ok (.Ok (fromMainArray x))
   | .ok (.Err e) => ok (.Err (fromMainError e))
   | .fail e => .fail e | .div => .div) = _
  rw [da]
 have lb : sourceDecode 29#usize low 29#usize=ok (.Ok (fromMainArray b)) := by
  unfold sourceDecode
  change (match AspisS1ExtractedRoundChildren.decodeMain 29#usize record 29#usize with
   | .ok (.Ok x) => ok (.Ok (fromMainArray x))
   | .ok (.Err e) => ok (.Err (fromMainError e))
   | .fail e => .fail e | .div => .div) = _
  rw [db]
 have lc : sourceDecode 29#usize low 58#usize=ok (.Ok (fromMainArray c)) := by
  unfold sourceDecode
  change (match AspisS1ExtractedRoundChildren.decodeMain 29#usize record 58#usize with
   | .ok (.Ok x) => ok (.Ok (fromMainArray x))
   | .ok (.Err e) => ok (.Err (fromMainError e))
   | .fail e => .fail e | .div => .div) = _
  rw [dc]
 refine ⟨⟨[fromMainArray a,fromMainArray b,fromMainArray c],by simp⟩,?_⟩
 rw [NJT_ClaimsRef_Value.reference]
 simp [NJT_ClaimsRef_Value.decode,called,AspisR1ClaimsUnrolledParent.decodeRows,
  NJT_ClaimsRef_Value.external,ClaimsUnrolledFinish.external,la,lb,lc]

/-- Named-allocator transport support on the exact caller domain. The still
missing native reserve/error/heap association is not a hypothesis here and is
not discharged by this theorem. It is recorded as OPEN in NJT_REMAINING. -/
theorem named_allocator {A : Type} (allocator : S2W_D189Wrappers.Allocator A)
 (initial : A) (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre)) :
 before (allocator.allocate initial 1392)
  (NJT_ClaimsRef_Value.unbox (NJT_ClaimsRef.r1_semantic.NJT_claims_ref
    (fromMainPrefix (PrefixAdapter.fromOld pre)))) =
 after (allocator.allocate initial 1392)
  (NJT_ClaimsRef_Value.unbox (NJT_ClaimsRef.r1_semantic.NJT_claims_ref
    (fromMainPrefix (PrefixAdapter.fromOld pre)))) := by
 obtain ⟨value,pure⟩:=pure_success bytes pre parsed
 rw [pure]
 exact commute _ _

#print axioms commute
#print axioms pure_success
#print axioms named_allocator
end AspisR1.NJT_AllocationLift
end
