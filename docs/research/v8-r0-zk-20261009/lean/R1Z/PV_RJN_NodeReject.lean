import R1Z.PV_RunJoin_QueryInvalidIndex56
import R1Z.PV_RunJoin_NodeSlot41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJN_NodeReject
open Aeneas Aeneas.Std Result ProverRwFull
abbrev badQueries := PV_RunJoin_QueryInvalidIndex56.badQueries

def badIndex : alloc.vec.Vec U32 := ⟨[262144#u32],by simp; scalar_tac⟩
def badSlice : Slice U32 := alloc.vec.Vec.deref badIndex

theorem indices : PV_RunJoin_PublishSkeleton54.indices badQueries 0 10 false=[262144] := by rfl

theorem unique (idx : alloc.vec.Vec U32) (h : idx.val.map UScalar.val=[262144]) : idx=badIndex := by
  apply Subtype.ext
  apply List.map_injective (f := fun x : U32 => x.val) (fun a b h => UScalar.eq_of_val_eq h)
  exact h

variable [ExternalTypes] [ExternalFuns]
/-- Exact native leaf constants and Option failure propagation. These are
helper laws, not a node serializer or model byte equality. -/
def PV_RJN_Producer_NodePrimitives : Prop :=
  multiproof.LEAF_BITS=ok 18#u32 ∧ multiproof.MAX_BATCH=ok 16#usize ∧
  (∀ T : Type, core.option.Option.Insts.CoreOpsTry_traitTry.branch (none : Option T)=
    ok (core.ops.control_flow.ControlFlow.Break none)) ∧
  (∀ T : Type, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual T none=ok none) ∧
  core.option.Option.ok_or (none : Option (alloc.vec.Vec U8)) verifier.Error.Allocation=ok (.Err .Allocation)

theorem body (bits : multiproof.LEAF_BITS=ok 18#u32) :
    host_tree.check_indices_loop.body badSlice 0#usize=ok (ControlFlow.done none) := by
  simp only [host_tree.check_indices_loop.body,
    show (0#usize)<Slice.len badSlice from by decide,if_true,
    show Slice.index_usize badSlice 0#usize=ok 262144#u32 from rfl,bits,bind_tc_ok,lift]
  rfl

theorem check (laws : PV_RJN_Producer_NodePrimitives) : host_tree.check_indices badSlice=ok none := by
  unfold host_tree.check_indices
  simp only [show core.slice.Slice.is_empty badSlice=ok false from rfl,bind_tc_ok,Bool.false_eq_true,if_false,
    laws.2.1,show ¬Slice.len badSlice>16#usize from by decide]
  unfold host_tree.check_indices_loop
  rw [ProverRw19LoopBind.loop_bind]
  simp only [body laws.1,bind_tc_ok]

theorem count (laws : PV_RJN_Producer_NodePrimitives) : host_tree.node_count badSlice=ok none := by
  simp only [host_tree.node_count,check laws,laws.2.2.1,bind_tc_ok,laws.2.2.2.1]

theorem tree (laws : PV_RJN_Producer_NodePrimitives) (t : host_tree.BinaryTree) :
    host_tree.BinaryTree.multiproof t badSlice=ok none := by
  simp only [host_tree.BinaryTree.multiproof,laws.1,lift,bind_tc_ok,count laws,
    laws.2.2.1,laws.2.2.2.1]

theorem first_slot (laws : PV_RJN_Producer_NodePrimitives) (out : alloc.vec.Vec U8)
    (cc1 cc2 : host_commitment.Commitment) (t : host_tree.BinaryTree)
    (idx : alloc.vec.Vec U32)
    (hidx : prover.publication_indices badQueries 0#usize compact.SPLIT false=ok idx)
    (hv : idx.val.map UScalar.val=[262144]) :
    prover.append_node_slot out cc1 cc2 t badQueries 0#usize 0#usize=ok (.Err .Allocation) := by
  have he := unique idx hv
  subst idx
  simp only [prover.append_node_slot,show (0#usize)=(0#usize) from rfl,if_true,bind_tc_ok,
    show ¬(0#usize)=(2#usize) from by decide,hidx,host_commitment.Commitment.multiproof,
    tree laws,laws.2.2.2.2,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rfl

theorem source (laws : PV_RJN_Producer_NodePrimitives) (out : alloc.vec.Vec U8)
    (cc1 cc2 : host_commitment.Commitment) (t : host_tree.BinaryTree)
    (idx : alloc.vec.Vec U32)
    (hidx : prover.publication_indices badQueries 0#usize compact.SPLIT false=ok idx)
    (hv : idx.val.map UScalar.val=[262144]) :
    prover.append_node_slots out cc1 cc2 t badQueries=ok (.Err .Allocation) := by
  simp only [prover.append_node_slots,first_slot laws out cc1 cc2 t idx hidx hv,
    core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rfl
#print axioms indices
#print axioms unique
#print axioms body
#print axioms check
#print axioms count
#print axioms tree
#print axioms first_slot
#print axioms source
end R1Z.PV_RJN_NodeReject
