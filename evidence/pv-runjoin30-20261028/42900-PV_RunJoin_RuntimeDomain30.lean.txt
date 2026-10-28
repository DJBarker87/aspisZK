import R1Z.BuilderAdmissionCommon
import R1Z.PV_RunJoin_BranchDomain28
import R1Z.PV_RunJoin_ControlDomain28
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RuntimeDomain30
open Aeneas Aeneas.Std Result AspisBuilderAdmissionSource
open R1Z.BuilderAdmissionStd
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28

def Path
  (public_pool : Array Std.U8 32#usize) (public_domain : Array Std.U8 32#usize)
  (anchor_sequence : Std.U64) (anchor : Array aspis_core.field.M31 8#usize)
  (nullifier : Array aspis_core.field.M31 8#usize)
  (asset : aspis_core.field.M31)
  (input : pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1)
  (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) : Prop :=
  ∃ b, (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 context.runtime_binding.pool public_pool) = ok b ∧
  if b
  then
    False
  else
    ∃ b1, (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 context.runtime_binding.deployment_domain public_domain) = ok b1 ∧
    if b1
    then
      False
    else
      if context.runtime_binding.anchor_sequence != anchor_sequence
      then
        False
      else
        ∃ b2, (core.array.equality.PartialEqArray.ne aspis_core.field.M31.Insts.CoreCmpPartialEqM31 context.runtime_binding.anchor_root anchor) = ok b2 ∧
        if b2
        then
          False
        else
          ∃ b3, (core.cmp.PartialEq.ne.trait_default aspis_core.field.M31.Insts.CoreCmpPartialEqM31 context.runtime_binding.asset_id asset) = ok b3 ∧
          if b3
          then
            False
          else
            ∃ b4, (core.slice.Slice.contains (Array.Insts.CoreCmpPartialEqArray 8#usize aspis_core.field.M31.Insts.CoreCmpPartialEqM31) context.spent_nullifiers nullifier) = ok b4 ∧
            if b4
            then
              False
            else
              ∃ b5, (pool_v1.pair_trace.digest_canonical input.nullifier_key) = ok b5 ∧
              if b5
              then
                ∃ b6, (pool_v1.pair_trace.digest_canonical input.salt) = ok b6 ∧
                if b6
                then
                  ∃ s, (lift (Array.to_slice input.membership.siblings)) = ok s ∧
                  ∃ i, (core.slice.Slice.iter s) = ok i ∧
                  ∃ b7, ∃ unused, (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any pool_v1.pair_trace.validate_common.closure.Insts.CoreOpsFunctionFnMutTupleSharedArrayM318Bool i ()) = ok (b7,unused) ∧
                  if b7
                  then
                    False
                  else
                    if input.value = 0#u32
                    then
                      False
                    else
                      ∃ i1, (spend.VALUE_LIMIT) = ok i1 ∧
                      if input.value >= i1
                      then
                        False
                      else
                        ∃ i2, (lift (Std.U32.wrapping_shl 1#u32 20#u32)) = ok i2 ∧
                        if input.membership.index >= i2
                        then
                          False
                        else
                          ∃ r, (pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.require_selected_spendable input.pair_leaf input.selected_second) = ok r ∧
                          wp (core.result.Result.map_err (BuiltinFnOnce pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1 pool_v1.pair_trace.PoolV1PairTraceErrorV1) r (pool_v1.pair_trace.PoolV1PairTraceErrorV1.PairLeafCtor)) isRustOk
                else
                  False
              else
                False

theorem success_iff
  (public_pool public_domain : Array U8 32#usize)
  (anchor_sequence : U64) (anchor nullifier : Array U32 8#usize)
  (asset : U32) (input : pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1)
  (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) :
  (∃ u, pool_v1.pair_trace.validate_common public_pool public_domain anchor_sequence
    anchor nullifier asset input context = ok (.Ok u)) ↔
  Path public_pool public_domain anchor_sequence anchor nullifier asset input context := by
  rw [success_wp]
  unfold pool_v1.pair_trace.validate_common Path
  simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,Prod.exists]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,Prod.exists])
#print axioms success_iff
end R1Z.PV_RunJoin_RuntimeDomain30
