import R1Z.PV_RunJoin_PublishContext57
import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EmptyTree59
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def empty : host_tree.BinaryTree := ⟨⟨[],by simp⟩⟩

theorem level (out : alloc.vec.Vec U8) (indices : alloc.vec.Vec U32)
    (bits : Usize) (nonzero : bits ≠ 0#usize) :
    host_tree.multiproof_levels empty out indices 0#usize bits=fail .arrayOutOfBounds := by
  rw [host_tree.multiproof_levels]
  simp only [Ne.symm nonzero,if_false]
  have first : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec (Array U8 32#usize)))
      empty.levels 0#usize=fail .arrayOutOfBounds := rfl
  rw [first]
  rfl

theorem no_multiproof (indices : Slice U32)
    (depth : multiproof.LEAF_BITS=ok 18#u8) (out : alloc.vec.Vec U8) :
    host_tree.BinaryTree.multiproof empty indices ≠ ok (some out) := by
  intro success
  unfold host_tree.BinaryTree.multiproof at success
  rw [depth] at success
  simp only [lift,bind_tc_ok] at success
  obtain ⟨count,hcount,tail⟩ := PV_RunJoin_ResultPost.bind_eq_ok success
  cases count with
  | none => cases tail
  | some n =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok,lift] at tail
    obtain ⟨copied,hcopy,tail⟩ := PV_RunJoin_ResultPost.bind_eq_ok tail
    rw [level _ copied _ (by scalar_tac)] at tail
    cases tail

#print axioms empty
#print axioms level
#print axioms no_multiproof
end R1Z.PV_RunJoin_EmptyTree59
