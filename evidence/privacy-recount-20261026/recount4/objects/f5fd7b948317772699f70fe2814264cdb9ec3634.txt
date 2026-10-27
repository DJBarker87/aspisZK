import R1Z.BuilderAdmissionCanonical

set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderAdmissionCommon
open Aeneas Aeneas.Std Result AspisBuilderAdmissionSource R0Z.WriterRefine
open pool_v1.pair_trace BuilderRecordsFields BuilderAdmissionRanges BuilderAdmissionCanonical
attribute [local instance] Classical.propDecidable

theorem mapErr_success {E V O : Type} (f : core.ops.function.FnOnce O E V)
    (r : core.result.Result Unit E) (c : O)
    (h : BuilderAdmissionStd.mapErr f r c = ok (.Ok ())) : r = .Ok () := by
  cases r with
  | Ok u => cases u; rfl
  | Err e =>
    unfold BuilderAdmissionStd.mapErr at h
    obtain ⟨e',_,h⟩ := bind_ok_inv h
    cases h

theorem selected_validates (p : pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1)
    (second : Bool) (h : p.require_selected_spendable second = ok (.Ok ())) :
    p.validate = ok (.Ok ()) := by
  unfold pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.require_selected_spendable at h
  obtain ⟨r,hr,h⟩ := bind_ok_inv h
  cases r with
  | Ok u => cases u; exact hr
  | Err e =>
    change (ok (core.result.Result.Err e) : Result (core.result.Result Unit
      pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1)) = ok (core.result.Result.Ok ()) at h
    cases h

/-- This is a theorem about success of the actual validator, not a record
subtype assuming the semantic spend relation. The forest-specific checks
and semantic digest/append meaning are deliberately not included. -/
structure CommonFacts (input : PoolV1PairInputNoteWitnessV1) : Prop where
  value_positive : 0 < input.value.val
  value_bound : input.value.val < 2^30
  index_bound : input.membership.index.val < 2^20
  key : Canon8 input.nullifier_key
  salt : Canon8 input.salt
  membership : ∀ l, l < 20 → Canon8 input.membership.siblings.val[l]!
  pair_first : Canon8 input.pair_leaf.first_commitment
  pair_second : Canon8 input.pair_leaf.second_commitment
  pair_validation : input.pair_leaf.validate = ok (.Ok ())

theorem common_facts
    (pool domain : Array U8 32#usize) (seq : U64) (anchor nullifier : Array U32 8#usize)
    (asset : U32) (input : PoolV1PairInputNoteWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (h : validate_common pool domain seq anchor nullifier asset input context = ok (.Ok ())) :
    CommonFacts input := by
  obtain ⟨hpositive,hvalue,hindex⟩ := validate_common_ranges pool domain seq anchor nullifier asset input context h
  unfold validate_common at h
  obtain ⟨b,_,h⟩ := bind_ok_inv h
  obtain ⟨_,h⟩ := error_then h
  obtain ⟨b1,_,h⟩ := bind_ok_inv h
  obtain ⟨_,h⟩ := error_then h
  obtain ⟨_,h⟩ := error_then h
  obtain ⟨b2,_,h⟩ := bind_ok_inv h
  obtain ⟨_,h⟩ := error_then h
  obtain ⟨b3,_,h⟩ := bind_ok_inv h
  obtain ⟨_,h⟩ := error_then h
  obtain ⟨b4,_,h⟩ := bind_ok_inv h
  obtain ⟨_,h⟩ := error_then h
  obtain ⟨b5,hb5,h⟩ := bind_ok_inv h
  obtain ⟨hb5',h⟩ := error_else h
  have hkey := digest_canonical_ok (by simpa only [hb5'] using hb5)
  obtain ⟨b6,hb6,h⟩ := bind_ok_inv h
  obtain ⟨hb6',h⟩ := error_else h
  have hsalt := digest_canonical_ok (by simpa only [hb6'] using hb6)
  simp only [lift, bind_tc_ok, core.slice.Slice.iter] at h
  obtain ⟨⟨b7,after⟩,hscan,h⟩ := bind_ok_inv h
  obtain ⟨hb7,h⟩ := error_then h
  obtain ⟨b8,a8,hscan',hscanSpec⟩ := siblings_scan input.membership.siblings
  rw [hscan] at hscan'
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj hscan')
  have hmembers := hscanSpec.mp (Bool.eq_false_iff.mpr hb7)
  obtain ⟨_,h⟩ := error_then h
  rw [value_limit] at h
  simp only [bind_tc_ok] at h
  obtain ⟨_,h⟩ := error_then h
  obtain ⟨_,h⟩ := error_then h
  obtain ⟨r,hr,h⟩ := bind_ok_inv h
  have hr' := mapErr_success _ r _ h
  rw [hr'] at hr
  have hv := selected_validates input.pair_leaf input.selected_second hr
  obtain ⟨hf,hs⟩ := pair_validate_canonical input.pair_leaf hv
  exact ⟨hpositive,hvalue,hindex,hkey,hsalt,hmembers,hf,hs,hv⟩

#print axioms mapErr_success
#print axioms selected_validates
#print axioms common_facts
end R1Z.BuilderAdmissionCommon
