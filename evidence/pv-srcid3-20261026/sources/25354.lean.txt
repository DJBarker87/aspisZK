import R1Z.PV_Src_AdmissionArray
import R1Z.PV_Src_AdmissionOccupied

/-! Forward execution of the extracted common validator with an empty spent
set and exact runtime binding. No source word-validity conclusion is assumed. -/
set_option autoImplicit false
namespace R1Z.PV_Src_AdmissionCommonSuccess
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderAdmissionSource
open pool_v1.pair_trace BuilderAdmissionCanonical PV_Src_AdmissionArray

abbrev Binding := pool_v1.payment_relation.PoolV1PaymentRuntimeBindingV1
abbrev Context := pool_v1.payment_relation.PoolV1PaymentRelationContextV1

def fresh (binding : Binding) : Context := ⟨binding,⟨[],by simp⟩⟩

theorem success (binding : Binding) (nullifier : Array U32 8#usize)
    (input : PoolV1PairInputNoteWitnessV1)
    (key : Canon8 input.nullifier_key) (salt : Canon8 input.salt)
    (membership : ∀ l, l < 20 → Canon8 input.membership.siblings.val[l]!)
    (positive : input.value ≠ 0#u32) (value : input.value.val < 2^30)
    (index : input.membership.index.val < 2^20)
    (pair : input.pair_leaf.require_selected_spendable input.selected_second = ok (.Ok ())) :
    validate_common binding.pool binding.deployment_domain binding.anchor_sequence
      binding.anchor_root nullifier binding.asset_id input (fresh binding) = ok (.Ok ()) := by
  classical
  change input.value.val < 1073741824 at value
  change input.membership.index.val < 1048576 at index
  obtain ⟨b,after,hscan,hs⟩ := siblings_scan input.membership.siblings
  have hb : b = false := hs.mpr membership
  rw [hb] at hscan
  have hword : core.cmp.PartialEq.ne.trait_default
      aspis_core.field.M31.Insts.CoreCmpPartialEqM31 binding.asset_id binding.asset_id = ok false := by
    simp [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
      aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]
  unfold validate_common
  dsimp only [fresh]
  rw [bytes_ne_self]
  simp [bind_tc_ok]
  rw [bytes_ne_self]
  simp [bind_tc_ok]
  rw [digest_ne_self,hword]
  simp only [bind_tc_ok,Bool.false_eq_true,↓reduceIte,core.slice.Slice.contains,List.anyM]
  rw [digest_canonical_eq]
  simp only [decide_eq_true key,bind_tc_ok,↓reduceIte]
  rw [digest_canonical_eq]
  simp only [decide_eq_true salt,bind_tc_ok,Bool.false_eq_true,↓reduceIte,lift,core.slice.Slice.iter]
  rw [hscan]
  simp only [bind_tc_ok,Bool.false_eq_true,↓reduceIte,positive]
  rw [BuilderAdmissionRanges.value_limit]
  simp only [bind_tc_ok]
  rw [if_neg (by simpa only [UScalar.le_equiv,UScalar.ofNatCore_val_eq] using Nat.not_le.mpr value)]
  try simp only [lift,bind_tc_ok]
  have shift : U32.wrapping_shl 1#u32 20#u32 = 1048576#u32 := rfl
  rw [shift,if_neg (by simpa only [UScalar.le_equiv,UScalar.ofNatCore_val_eq] using Nat.not_le.mpr index),pair]
  rfl

#print axioms success
end R1Z.PV_Src_AdmissionCommonSuccess
