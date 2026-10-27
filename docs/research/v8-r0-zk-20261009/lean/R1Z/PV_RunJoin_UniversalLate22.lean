import R1Z.PV_Src_NativeInput
import R1Z.BuilderBankShape
set_option autoImplicit false
namespace R1Z.PV_RunJoin_UniversalLate22
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1

theorem scalar_ne_self (x : U32) : core.cmp.PartialEq.ne.trait_default
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31 x x = ok false := by
  simp only [core.cmp.PartialEq.ne.trait_default,
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31]
  with_unfolding_all simp [core.cmp.PartialEq.ne.default,aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]
#print axioms scalar_ne_self

def compare (p : U32 × U32) : Result Bool := do
  let b ← aspis_core.field.M31.Insts.CoreCmpPartialEqM31.ne p.1 p.2
  ok (decide (¬ b = true))

theorem compare_self (x : U32) : compare (x,x) = ok true := by
  change (do
    let b ← core.cmp.PartialEq.ne.trait_default aspis_core.field.M31.Insts.CoreCmpPartialEqM31 x x
    ok (decide (¬ b = true))) = _
  rw [scalar_ne_self]
  rfl
#print axioms compare_self

theorem diagonal (xs : List U32) : List.allM compare (xs.zip xs) = ok true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.allM,compare_self,ih]
#print axioms diagonal

theorem eq_self (d : Array U32 8#usize) : core.array.equality.PartialEqArray.eq
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31 d d = ok true := by
  rw [core.array.equality.PartialEqArray.eq,if_pos rfl]
  exact diagonal d.val
#print axioms eq_self

/-- Array equality is a symbolic source fact for every word array. -/
theorem ne_self (d : Array U32 8#usize) :
    core.array.equality.PartialEqArray.ne aspis_core.field.M31.Insts.CoreCmpPartialEqM31 d d = ok false := by
  rw [core.array.equality.PartialEqArray.ne,eq_self]
  rfl
#print axioms ne_self

/-- Lift late_append's final join for arbitrary snapshots and arbitrary
constructor/append outputs. No index-zero or fixture specialization. The
constructor and append laws stay explicit pending the general tree proof. -/
theorem source [ExternalLinear]
    (records : pair_forest_copy_builder.CopyRecords)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (leaf : Array U32 8#usize) (roots : Array (Array U32 8#usize) 21#usize)
    (tree after : incremental_merkle.IncrementalMerkleTreeV1)
    (receipt : incremental_merkle.AppendOneV1)
    (sequence : snapshot.sequence = snapshot.next_pair_index)
    (root_call : pair_trace.pair_empty_roots = ok roots)
    (construct : incremental_merkle.IncrementalMerkleTreeV1.from_parts_with_empty_roots
      snapshot.next_pair_index snapshot.current_root snapshot.frontier roots = ok (.Ok tree))
    (append : incremental_merkle.IncrementalMerkleTreeV1.append_one_with_empty_roots tree leaf roots =
      ok (.Ok (after,receipt)))
    (copy_root : pair_forest_copy_builder.CopyRecords.append_root records = ok after.root) :
    pair_forest_trace.late_append records snapshot leaf = ok (.Ok {
      next_pair_index := after.next_leaf_index,next_root := after.root,next_frontier := after.frontier }) := by
  rw [pair_forest_trace.late_append,sequence]
  simp only [bne_self_eq_false,↓reduceIte]
  rw [root_call]
  simp only [bind_tc_ok]
  rw [construct]
  simp only [bind_tc_ok,BuilderForestStdPort.core.result.Result.map_err,
    BuilderAdmissionStd.mapErr,core.result.Result.Insts.CoreOpsTry.branch]
  rw [append]
  simp only [bind_tc_ok,BuilderForestStdPort.core.result.Result.map_err,
    BuilderAdmissionStd.mapErr,core.result.Result.Insts.CoreOpsTry.branch]
  rw [copy_root]
  simp only [bind_tc_ok]
  rw [ne_self]
  rfl
#print axioms source
end R1Z.PV_RunJoin_UniversalLate22
