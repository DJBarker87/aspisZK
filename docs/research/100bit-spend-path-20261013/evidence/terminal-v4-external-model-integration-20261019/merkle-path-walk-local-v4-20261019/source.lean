import AspisR1MerklePathChildren.Funs
import OccupancyRangeTraversal

/-! Successful execution of the actual emitted six-iteration Merkle checker
supplies its own sequence of successful source steps. No path-execution
predicate is assumed as an input. -/
set_option autoImplicit false
namespace AspisR1MerklePathChildren.RawMerklePathWalk
open Aeneas Aeneas.Std Result ControlFlow
abbrev Digest := Array U8 32#usize
abbrev Range := core.ops.range.Range Usize

def step {H : Type} (D : Digest32 H) (hash : H) (path : Slice U8)
    (d index : Usize) (node : Digest) : Result (Usize × Digest) := do
  let slot ← index % 8#usize
  let a0 ← verifier.merkle_child slot node path d 0#usize
  let a1 ← verifier.merkle_child slot node path d 1#usize
  let a2 ← verifier.merkle_child slot node path d 2#usize
  let a3 ← verifier.merkle_child slot node path d 3#usize
  let a4 ← verifier.merkle_child slot node path d 4#usize
  let a5 ← verifier.merkle_child slot node path d 5#usize
  let a6 ← verifier.merkle_child slot node path d 6#usize
  let a7 ← verifier.merkle_child slot node path d 7#usize
  let next ← merkle.parent_with_digest D hash
    (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7])
  let nextIndex ← index / 8#usize
  ok (nextIndex,next)

theorem loop_unroll {H : Type} (D : Digest32 H) (hash : H)
    (path : Slice U8) (iter : Range) (index : Usize) (node : Digest) :
    verifier.merkle_path_loop D iter hash index node path = (do
      let flow ← verifier.merkle_path_loop.body D hash path iter index node
      match flow with
      | cont (iter1,index1,node1) => verifier.merkle_path_loop D iter1 hash index1 node1 path
      | done out => ok out) := by
  conv_lhs => unfold verifier.merkle_path_loop; rw [loop]
  cases hb : verifier.merkle_path_loop.body D hash path iter index node with
  | fail e => simp only [hb,bind_tc_fail]
  | div => simp only [hb,bind_tc_div]
  | ok flow =>
    cases flow with
    | done out => simp only [hb,bind_tc_ok]
    | cont next => simp only [hb,bind_tc_ok]; rfl

theorem body_factor {H : Type} (D : Digest32 H) (hash : H)
    (path : Slice U8) (iter : Range) (index : Usize) (node : Digest) :
    verifier.merkle_path_loop.body D hash path iter index node = (do
      let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok (done (index,node))
      | some d =>
        let (index1,node1) ← step D hash path d index node
        ok (cont (iter1,index1,node1))) := by
  simp only [verifier.merkle_path_loop.body,step,bind_assoc_eq,bind_tc_ok]
  rfl

theorem loop_equation {H : Type} (D : Digest32 H) (hash : H)
    (path : Slice U8) (iter : Range) (index : Usize) (node : Digest) :
    verifier.merkle_path_loop D iter hash index node path = (do
      let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok (index,node)
      | some d =>
        let (index1,node1) ← step D hash path d index node
        verifier.merkle_path_loop D iter1 hash index1 node1 path) := by
  rw [loop_unroll,body_factor]
  simp only [bind_assoc_eq]
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e => simp only [hn,bind_tc_fail]
  | div => simp only [hn,bind_tc_div]
  | ok result =>
    rcases result with ⟨o,iter1⟩
    cases o with
    | none => simp only [hn,bind_tc_ok]; rfl
    | some d =>
      simp only [hn,bind_tc_ok,bind_assoc_eq]
      try dsimp only
      cases hs : step D hash path d index node with
      | fail e => simp only [hs,bind_tc_fail]
      | div => simp only [hs,bind_tc_div]
      | ok next => rcases next with ⟨i,n⟩; simp only [hs,bind_tc_ok]; rfl

inductive Walk {H : Type} (D : Digest32 H) (hash : H) (path : Slice U8) :
    Nat → Nat → Usize → Digest → Usize → Digest → Prop where
  | nil (depth : Nat) (index : Usize) (node : Digest) :
      Walk D hash path 0 depth index node index node
  | cons {count depth : Nat} {index index1 index2 : Usize} {node node1 node2 : Digest}
      (d : Usize) (hd : d.val = depth)
      (hs : step D hash path d index node = ok (index1,node1))
      (tail : Walk D hash path count (depth+1) index1 node1 index2 node2) :
      Walk D hash path (count+1) depth index node index2 node2

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Invert successful actual loop execution, with symbolic fuel rather than
unfolding six copies of the checker or any concrete hash arithmetic. -/
theorem loop_success_walk {H : Type} (D : Digest32 H) (hash : H) (path : Slice U8)
    (count : Nat) (iter : Range) (index : Usize) (node : Digest)
    (outIndex : Usize) (outNode : Digest)
    (hend : iter.end.val = 6) (hspan : iter.start.val + count = 6)
    (h : verifier.merkle_path_loop D iter hash index node path = ok (outIndex,outNode)) :
    Walk D hash path count iter.start.val index node outIndex outNode := by
  induction count generalizing iter index node with
  | zero =>
    have hdone : iter.start.val ≥ iter.end.val := by omega
    rw [loop_equation, AspisR1.OccupancyRangeTraversal.next_done iter hdone] at h
    simp only [bind_tc_ok] at h
    cases Result.ok.inj h
    exact .nil _ _ _
  | succ count ih =>
    have hlt : iter.start.val < iter.end.val := by omega
    obtain ⟨iter1,hnext,hstart,hend1,_⟩ :=
      AspisR1.OccupancyRangeTraversal.next_step iter hlt
    rw [loop_equation,hnext] at h
    simp only [bind_tc_ok] at h
    obtain ⟨⟨index1,node1⟩,hs,hrest⟩ := bind_success _ _ _ h
    exact .cons iter.start rfl hs
      (by simpa only [hstart] using
        ih iter1 index1 node1 (by simpa only [hend1] using hend) (by omega) hrest)

#print axioms loop_equation
#print axioms loop_success_walk
end AspisR1MerklePathChildren.RawMerklePathWalk
