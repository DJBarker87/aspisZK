import NJT_ClaimsCohort
import NJT_QClaimsCanonical
import NJG_ClaimsGeometry
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJT_ClaimsRoot
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open ClaimsUnrolledFinish

/-- Whole emitted owned-reference Result after the singleton carrier conversion.
Every operation is fixed; no successful allocation or decoder result is input. -/
theorem reference (pre : MainPrefix) :
 toMainStatus (NJT_ClaimsRef_Value.unbox
  (NJT_ClaimsRef.r1_semantic.NJT_claims_ref (fromMainPrefix pre))) =
 claims NJT_ClaimsRef_Value.std pre := by
 exact congrArg toMainStatus (NJT_ClaimsCohort.reference (fromMainPrefix pre))

def Packet (bytes : Slice U8) : Prop :=
 match AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
 | .ok (.Ok pre) =>
   toMainStatus (NJT_ClaimsRef_Value.unbox
    (NJT_ClaimsRef.r1_semantic.NJT_claims_ref (fromMainPrefix (PrefixAdapter.fromOld pre)))) =
   claims NJT_ClaimsRef_Value.std (PrefixAdapter.fromOld pre) ∧
   ∃ record,r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) 25#u8=ok (.Ok record) ∧
    record.row=25#u8 ∧ record.framed.val.length=3717 ∧
    ∀ (p off : Usize),p.val<3 → off.val=p.val*29 →
     ∃ out,AspisS1ExtractedRoundChildren.decodeMain 29#usize record off=ok (.Ok out)
 | _ => True

/-- Actual private invocation root. Parser failure is non-entry. For every
entered call, all three decoder successes and exact frame length are derived
from that SAME parsed input, before commuting the allocation phase. -/
theorem claims (bytes : Slice U8) : Packet bytes := by
 unfold Packet
 generalize parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes = result
 cases result with
 | fail e => trivial
 | div => trivial
 | ok result =>
  cases result with
  | Err e => trivial
  | Ok pre =>
   refine ⟨reference _,?_⟩
   obtain ⟨record,getter,row,decoded⟩:=NJT_QClaimsCanonical.claims bytes pre parsed
   obtain ⟨same,call,tag,framed⟩:=NJG_ClaimsGeometry.producer bytes pre parsed
   have equal : same=record := core.result.Result.Ok.inj (Result.ok.inj (call.symm.trans getter))
   subst same
   exact ⟨record,getter,row,framed,decoded⟩

/-- Pure successful decodes commute with the SAME allocator action, including
its error/failure/divergence and full returned allocator state. This generic
support law has no allocation-success premise and adds no trust. -/
theorem allocation_transport {A B C : Type} (allocation : Result A) (value : B)
 (next : A → B → Result C) :
 (do let allocated ← allocation; let decoded ← ok value; next allocated decoded) =
 (do let decoded ← ok value; let allocated ← allocation; next allocated decoded) := by
 cases allocation <;> rfl

#print axioms reference
#print axioms claims
#print axioms allocation_transport
#check @claims
end AspisR1.NJT_ClaimsRoot
end
