import NKF_Windows
set_option autoImplicit false
noncomputable section
namespace NKF_LaneConstructor
open Aeneas Aeneas.Std Result
abbrev Lane := AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1
abbrev Tree := AdapterRw.aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1
/-- K067 is retired. The replacement splits scalar/header, root, and one
frontier-row window. A native matched control for those windows is OPEN. -/
structure Fields (a b : Lane) : Prop where
 bump : a.bump=b.bump
 master : NKF_Windows.Bounded a.master b.master
 lane : a.lane_id=b.lane_id
 next : a.tree.next_leaf_index=b.tree.next_leaf_index
 root : NKF_Windows.WordWindow a.tree.root b.tree.root
 frontier : ∀ i : Nat, ∀ ha : i<a.tree.frontier.val.length,
   ∀ hb : i<b.tree.frontier.val.length,
   NKF_Windows.WordWindow (a.tree.frontier.val[i]'ha) (b.tree.frontier.val[i]'hb)

theorem tree (a b : Tree) (next : a.next_leaf_index=b.next_leaf_index)
 (root : a.root=b.root)
 (frontier : NKF_ArrayFrame.CellEq a.frontier b.frontier) : a=b := by
 have same:=NKF_ArrayFrame.array_ext _ _ frontier
 cases a; cases b
 simp only at next root same
 cases next;cases root;cases same;rfl

theorem constructor (a b : Lane) (fields : Fields a b) : a=b := by
 have hm:=NKF_ArrayFrame.array_ext _ _ (NKF_Windows.bounded_cells _ _ fields.master)
 have hr:=NKF_ArrayFrame.array_ext _ _ (NKF_Windows.word_cells _ _ fields.root)
 have hf : a.tree.frontier=b.tree.frontier := by
  apply NKF_ArrayFrame.array_ext
  intro i
  by_cases ha : i<a.tree.frontier.val.length
  · have hb : i<b.tree.frontier.val.length := by
     have al:=a.tree.frontier.property
     have bl:=b.tree.frontier.property
     omega
    have row:=NKF_ArrayFrame.array_ext _ _ (NKF_Windows.word_cells _ _ (fields.frontier i ha hb))
    simpa only [List.getElem?_eq_getElem ha,List.getElem?_eq_getElem hb] using congrArg some row
  · have hb : ¬i<b.tree.frontier.val.length := by
     have al:=a.tree.frontier.property
     have bl:=b.tree.frontier.property
     omega
    have outa : a.tree.frontier.val.length ≤ i := by omega
    have outb : b.tree.frontier.val.length ≤ i := by omega
    rw [List.getElem?_eq_none outa,List.getElem?_eq_none outb]
 have ht:=tree _ _ fields.next hr (by rw [hf];intro i;rfl)
 have hbum:=fields.bump
 have hl:=fields.lane
 cases a;cases b
 simp only at hm ht hbum hl
 cases hbum;cases hm;cases hl;cases ht;rfl
#print axioms tree
set_option pp.proofs false in
#print constructor
#print axioms constructor
end NKF_LaneConstructor
