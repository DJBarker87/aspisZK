import R1Z.PV_RunJoin_LateAppendFrame31
import R1Z.PV_RunJoin_ForestEquality30
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SnapshotRoot31
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_UniversalTreeFrame22

theorem equal_of_eq (a b : Digest)
    (h : core.array.equality.PartialEqArray.eq aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a b = ok true) : a=b := by
  apply PV_RunJoin_ForestEquality30.equal a b
  rw [core.array.equality.PartialEqArray.ne,h]
  rfl
#print axioms equal_of_eq

def read [ExternalLinear] (tree : incremental_merkle.IncrementalMerkleTreeV1) (roots : Roots) :
    Result (core.result.Result Digest incremental_merkle.PoolV1TreeError) :=
  if tree.next_leaf_index = 0#u64 then do
    let root ← Array.index_usize roots format.POOL_V1_TREE_DEPTH
    ok (.Ok root)
  else tree.reconstruct_nonfull_root roots

/-- Reconstruction reads index/frontier/empty roots; it does not read the
candidate root. This unfolds only the symbolic call spine, not a hash or loop. -/
theorem frame [ExternalLinear] (index : U64) (frontier : Frontier) (roots : Roots)
    (a b : Digest) : read ⟨index,a,frontier⟩ roots = read ⟨index,b,frontier⟩ roots := rfl
#print axioms frame

theorem checked [ExternalLinear] (tree : incremental_merkle.IncrementalMerkleTreeV1)
    (roots : Roots) (capacity : U64)
    (hcapacity : incremental_merkle.POOL_V1_LEAF_CAPACITY = ok capacity)
    (small : tree.next_leaf_index < capacity)
    (h : incremental_merkle.tree_reference.validate_owned tree roots = ok (.Ok ())) :
    read tree roots = ok (.Ok tree.root) := by
  rw [incremental_merkle.tree_reference.validate_owned,hcapacity] at h
  simp only [bind_tc_ok] at h
  rw [if_neg (by scalar_tac)] at h
  pv_peel h with scanned hscan
  pv_peel h with flow hflow
  cases flow with
  | Break residual => exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
  | Continue value =>
    by_cases zero : tree.next_leaf_index = 0#u64
    · rw [if_pos zero] at h
      rw [read,if_pos zero]
      pv_peel h with root hr
      pv_peel h with equal he
      cases equal <;> simp only [Bool.false_eq_true,↓reduceIte] at h
      · cases h
      · have same := equal_of_eq tree.root root he
        rw [hr]
        simp only [bind_tc_ok,same]
    · rw [if_neg zero,if_pos small] at h
      rw [read,if_neg zero]
      pv_peel h with result hr
      pv_peel h with flow hflow
      cases flow with
      | Break residual => exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
      | Continue root =>
        have returned := PV_RunJoin_DecoderReturn29.branch_continue result root hflow
        cases returned
        pv_peel h with different hd
        cases different <;> simp only [Bool.false_eq_true,↓reduceIte] at h
        · have same := PV_RunJoin_ForestEquality30.equal root tree.root hd
          rw [same] at hr
          exact hr
        · cases h
#print axioms checked
end R1Z.PV_RunJoin_SnapshotRoot31
