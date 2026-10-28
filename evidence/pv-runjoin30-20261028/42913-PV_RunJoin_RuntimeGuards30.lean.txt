import R1Z.PV_RunJoin_RuntimePrimitives30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RuntimeGuards30
open Aeneas Aeneas.Std Result AspisBuilderAdmissionSource R0Z.WriterRefine
open pool_v1.pair_trace
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def Runtime (pool domain : Array U8 32#usize) (seq : U64)
    (anchor : Array U32 8#usize) (asset : U32)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) : Prop :=
  context.runtime_binding.pool=pool ∧ context.runtime_binding.deployment_domain=domain ∧
  context.runtime_binding.anchor_sequence=seq ∧ context.runtime_binding.anchor_root=anchor ∧
  context.runtime_binding.asset_id=asset

def Digests (input : PoolV1PairInputNoteWitnessV1) : Prop :=
  Canon8 input.nullifier_key ∧ Canon8 input.salt ∧
    ∀ l, l < 20 → Canon8 input.membership.siblings.val[l]!

def Values (input : PoolV1PairInputNoteWitnessV1) : Prop :=
  0 < input.value.val ∧ input.value.val < 2^30 ∧ input.membership.index.val < 2^20

def result (pool domain : Array U8 32#usize) (seq : U64)
    (anchor nullifier : Array U32 8#usize) (asset : U32)
    (input : PoolV1PairInputNoteWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) :
    Result (core.result.Result Unit PoolV1PairTraceErrorV1) :=
  if ¬ Runtime pool domain seq anchor asset context then ok (.Err .RuntimeBinding)
  else if nullifier ∈ context.spent_nullifiers.val then ok (.Err .NullifierAlreadySpent)
  else if ¬ Digests input then ok (.Err .WitnessDigest)
  else if ¬ Values input then ok (.Err .ValueOutOfRange)
  else do
    let r ← input.pair_leaf.require_selected_spendable input.selected_second
    core.result.Result.map_err (BuiltinFnOnce
      pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1 PoolV1PairTraceErrorV1)
      r PoolV1PairTraceErrorV1.PairLeafCtor

theorem source_result (pool domain : Array U8 32#usize) (seq : U64)
    (anchor nullifier : Array U32 8#usize) (asset : U32)
    (input : PoolV1PairInputNoteWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) :
    validate_common pool domain seq anchor nullifier asset input context =
      result pool domain seq anchor nullifier asset input context := by
  obtain ⟨b,after,hs,hb⟩ := BuilderAdmissionCanonical.siblings_scan input.membership.siblings
  unfold validate_common
  simp only [PV_RunJoin_RuntimePrimitives30.bytes_ne,
    PV_RunJoin_RuntimePrimitives30.array_ne,PV_RunJoin_RuntimePrimitives30.word_ne,
    PV_RunJoin_RuntimePrimitives30.contains,BuilderAdmissionCanonical.digest_canonical_eq,
    lift,bind_tc_ok,core.slice.Slice.iter,hs,BuilderAdmissionRanges.value_limit]
  unfold result Runtime Digests Values
  simp only [decide_eq_true_eq,UScalar.le_equiv,UScalar.ofNatCore_val_eq]
  have hz : input.value = 0#u32 ↔ input.value.val=0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact UScalar.eq_of_val_eq h
  have hshift : U32.wrapping_shl 1#u32 20#u32 = 1048576#u32 := rfl
  rw [hshift]
  simp only [UScalar.le_equiv,UScalar.ofNatCore_val_eq,hz]
  split_ifs <;> simp_all
  all_goals omega
#print axioms source_result
end R1Z.PV_RunJoin_RuntimeGuards30
