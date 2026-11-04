import R1Z.BuilderAdmissionExtracted
import R1Z.BuilderRecordsFields

set_option autoImplicit false
namespace R1Z.BuilderAdmissionRanges
open Aeneas Aeneas.Std Result AspisBuilderAdmissionSource
open pool_v1.pair_trace R1Z.BuilderRecordsFields

theorem value_limit : spend.VALUE_LIMIT = ok 1073741824#u32 := by
  rw [spend.VALUE_LIMIT]
  rfl

theorem error_then {E : Type} {p : Prop} [Decidable p] {e : E}
    {rest : Result (core.result.Result Unit E)}
    (h : (if p then ok (.Err e) else rest) = ok (.Ok ())) :
    ¬p ∧ rest = ok (.Ok ()) := by
  by_cases hp : p
  · rw [if_pos hp] at h
    cases h
  · exact ⟨hp, by simpa only [if_neg hp] using h⟩

theorem error_else {E : Type} {p : Prop} [Decidable p] {e : E}
    {rest : Result (core.result.Result Unit E)}
    (h : (if p then rest else ok (.Err e)) = ok (.Ok ())) :
    p ∧ rest = ok (.Ok ()) := by
  by_cases hp : p
  · exact ⟨hp, by simpa only [if_pos hp] using h⟩
  · rw [if_neg hp] at h
    cases h

/-- Primitive value/index bounds follow from successful execution of the
actual extracted validation function, with every earlier rejection retained. -/
theorem validate_common_ranges
    (pool domain : Array U8 32#usize) (seq : U64) (anchor nullifier : Array U32 8#usize)
    (asset : U32) (input : PoolV1PairInputNoteWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (h : validate_common pool domain seq anchor nullifier asset input context =
      ok (.Ok ())) :
    0 < input.value.val ∧ input.value.val < 2^30 ∧ input.membership.index.val < 2^20 := by
  unfold validate_common at h
  obtain ⟨b, _, h⟩ := bind_ok_inv h
  obtain ⟨_, h⟩ := error_then h
  obtain ⟨b1, _, h⟩ := bind_ok_inv h
  obtain ⟨_, h⟩ := error_then h
  obtain ⟨_, h⟩ := error_then h
  obtain ⟨b2, _, h⟩ := bind_ok_inv h
  obtain ⟨_, h⟩ := error_then h
  obtain ⟨b3, _, h⟩ := bind_ok_inv h
  obtain ⟨_, h⟩ := error_then h
  obtain ⟨b4, _, h⟩ := bind_ok_inv h
  obtain ⟨_, h⟩ := error_then h
  obtain ⟨b5, _, h⟩ := bind_ok_inv h
  obtain ⟨_, h⟩ := error_else h
  obtain ⟨b6, _, h⟩ := bind_ok_inv h
  obtain ⟨_, h⟩ := error_else h
  obtain ⟨s, _, h⟩ := bind_ok_inv h
  obtain ⟨i, _, h⟩ := bind_ok_inv h
  obtain ⟨⟨b7, after⟩, _, h⟩ := bind_ok_inv h
  obtain ⟨_, h⟩ := error_then h
  obtain ⟨hnz, h⟩ := error_then h
  rw [value_limit] at h
  simp only [bind_tc_ok] at h
  obtain ⟨hval, h⟩ := error_then h
  simp only [lift, bind_tc_ok] at h
  obtain ⟨hindex, _⟩ := error_then h
  have hz : input.value.val ≠ 0 := by
    intro e
    apply hnz
    exact UScalar.eq_of_val_eq (by simpa using e)
  have hshift : U32.wrapping_shl 1#u32 20#u32 = 1048576#u32 := rfl
  rw [hshift] at hindex
  simp only [UScalar.le_equiv, UScalar.ofNatCore_val_eq] at hval hindex
  exact ⟨Nat.pos_of_ne_zero hz, Nat.lt_of_not_ge hval, Nat.lt_of_not_ge hindex⟩

#print axioms error_then
#print axioms error_else
#print axioms value_limit
#print axioms validate_common_ranges
end R1Z.BuilderAdmissionRanges
