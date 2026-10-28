import NDO_JHi_RawFrontierCheck
set_option autoImplicit false
namespace AspisR1.JHi_RawSnapshotValidator
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct
open aspis_statement.pool_v1.pair_tree_profile

theorem capacity : POOL_V1_PAIR_CAPACITY=ok 1048576#u64 := by
  unfold POOL_V1_PAIR_CAPACITY POOL_V1_PAIR_TREE_DEPTH
  rfl

theorem source (s : PoolV1PairLiveSnapshotV1)
    (pool : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.pool (Array.repeat 32#usize 0#u8)=ok false)
    (domain : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.deployment_domain (Array.repeat 32#usize 0#u8)=ok false)
    (sequence : s.sequence=s.next_pair_index) (small : s.next_pair_index.val<1048576)
    (root : JFu_DigestCanonical.Canonical s.current_root)
    (frontier : ∀ i : Fin 20,JFu_DigestCanonical.Canonical
      (s.frontier.val[i.val]'(by simpa only [s.frontier.property,show (20#usize).val=20 from rfl] using i.isLt))) :
    validate_pool_v1_pair_live_snapshot_v1 s=ok (.Ok ()) := by
  unfold validate_pool_v1_pair_live_snapshot_v1
  dsimp only
  rw [pool,bind_tc_ok]
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [domain,bind_tc_ok]
  simp only [Bool.false_eq_true,↓reduceIte]
  have check : ¬s.next_pair_index ≥ 1048576#u64 := by scalar_tac
  have seqCheck : (s.sequence != s.next_pair_index)=false := by simp [sequence]
  simp only [seqCheck,Bool.false_eq_true,↓reduceIte,capacity,bind_tc_ok,if_neg check]
  rw [JHi_ProfileDigestAssociation.canonical s.current_root root,bind_tc_ok]
  simp only [↓reduceIte]
  exact JHi_RawFrontierCheck.source s.frontier frontier

#print axioms capacity
#print axioms source
end AspisR1.JHi_RawSnapshotValidator
