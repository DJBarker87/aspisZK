import NBG_Atomic
import NBG_Utilities
set_option autoImplicit false
noncomputable section
namespace NBG_PaymentChecks
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev E := pool_v1.payment_relation.PoolV1PaymentStatementFormatError

def canonical (d : Array U32 8#usize) : Bool :=
  d.val.all (fun x => decide (x.val < 2147483647))

theorem canonical_result (d : Array U32 8#usize) :
    pool_v1.payment_relation.digest_is_canonical d = ok (canonical d) := by
  obtain ⟨a,b,c,e,f,g,h,i,same⟩ := NBG_Utilities.shape d
  subst d
  unfold NBG_Utilities.pack
  rw [NBG_Atomic.digest_canonical]
  simp [canonical,NBG_Utilities.pack,Array.make]

def zero (a : Array U8 32#usize) : Bool := decide (a.val = List.replicate 32 0#u8)

theorem zero_result (a : Array U8 32#usize) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a
      (Array.repeat 32#usize 0#u8) = ok (zero a) := by
  unfold core.array.equality.PartialEqArray.eq
  rw [if_pos (a.property.trans (Array.repeat 32#usize 0#u8).property.symm)]
  rw [NBG_Utilities.lists a.val (Array.repeat 32#usize 0#u8).val
    (a.property.trans (Array.repeat 32#usize 0#u8).property.symm)]
  rfl

theorem capacity_result : pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY =
    ok 1048576#u64 := by
  unfold pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY pool_v1.format.POOL_V1_TREE_DEPTH
  rfl

def common (c : C) : core.result.Result Unit E :=
  if zero c.pool || zero c.deployment_domain then .Err .ZeroRequiredBinding
  else if c.anchor_sequence.val > 1048576 then .Err .InvalidAnchorSequence
  else if !canonical c.anchor_root || !canonical c.nullifier then .Err .NonCanonicalDigest
  else if c.asset_id.val >= 2147483647 then .Err .NonCanonicalAssetId
  else .Ok ()

theorem common_result (c : C) :
    pool_v1.payment_relation.validate_common c = ok (common c) := by
  simp [pool_v1.payment_relation.validate_common,zero_result,capacity_result,
    canonical_result,common,aspis_core.field.P]
  repeat' split
  all_goals simp_all

#print axioms canonical_result
#print axioms zero_result
#print axioms capacity_result
#print axioms common_result
end NBG_PaymentChecks
