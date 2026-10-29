import R1Z.PV_RunJoin_PublishSkeleton57
import R1Z.PV_RunJoin_QueryNativeObstruction56
import R1Z.PV_RunJoin_EncoderFields49
import R1Z.PV_RunJoin_FibreFillThread43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryEmptyWords57
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
variable [ExternalTypes] [ExternalFuns]

/-- One lane but no corresponding word. Fields does not inspect either. -/
def broken (tree : host_tree.BinaryTree) : host_commitment.Commitment :=
  ⟨.C1,⟨[0#usize],by simp; scalar_tac⟩,⟨[],by simp⟩,tree,none⟩

theorem lane (tree : host_tree.BinaryTree) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Usize)
      (broken tree).lanes 0#usize=ok 0#usize := by rfl

theorem word (tree : host_tree.BinaryTree) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice host_commitment.Word)
      (broken tree).words 0#usize=fail .arrayOutOfBounds := by rfl

theorem fill (tree : host_tree.BinaryTree) (u : aspis_core.r0.domain.FibreIndex)
    (opening : aspis_core.r0.wire.FibreOpening) :
    host_commitment.Commitment.fill_opening (broken tree) u opening=fail .arrayOutOfBounds := by
  unfold host_commitment.Commitment.fill_opening
  rw [host_commitment.fill_opening_values]
  simp only [show (0#usize)≠alloc.vec.Vec.len (broken tree).lanes from by change (0#usize)≠1#usize; scalar_tac,
    if_false,lane,word,bind_tc_ok,bind_tc_fail]

#print axioms broken
#print axioms lane
#print axioms word
#print axioms fill
end R1Z.PV_RunJoin_QueryEmptyWords57
