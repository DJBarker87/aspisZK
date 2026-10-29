import R1Z.PV_RunJoin_NodeSixReads60
import R1Z.PV_RunJoin_NodeSequence60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NodeSixSequence60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
variable [ExternalTypes] [ExternalFuns]

def inputs (cc1 cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree)
    (queries : Array U32 22#usize) : List PV_RunJoin_NodeSequence60.Input :=
  [(PV_RunJoin_NodePayload60.payload cc1 cc2 tree queries 0#usize 0#usize,4672#usize),
   (PV_RunJoin_NodePayload60.payload cc1 cc2 tree queries 0#usize 1#usize,4672#usize),
   (PV_RunJoin_NodePayload60.payload cc1 cc2 tree queries 0#usize 2#usize,4096#usize),
   (PV_RunJoin_NodePayload60.payload cc1 cc2 tree queries 1#usize 0#usize,5504#usize),
   (PV_RunJoin_NodePayload60.payload cc1 cc2 tree queries 1#usize 1#usize,5504#usize),
   (PV_RunJoin_NodePayload60.payload cc1 cc2 tree queries 1#usize 2#usize,4800#usize)]

theorem source (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (out : alloc.vec.Vec U8)
    (cc1 cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree) (queries : Array U32 22#usize) :
    @prover.append_node_slots (types base) (selected base heap box ops) out cc1 cc2 tree queries=
      PV_RunJoin_NodeSequence60.run (@inputs (types base) (selected base heap box ops) cc1 cc2 tree queries) out := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  unfold inputs prover.append_node_slots
  rw [PV_RunJoin_NodeSlotRead60.source out cc1 cc2 tree queries 0#usize 0#usize 4672#usize
    (PV_RunJoin_NodeSixReads60.read00 base heap box ops)]
  apply PV_RunJoin_ResultBindEq55.complete
  intro status0
  cases status0 with
  | Err e => rfl
  | Ok next0 =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    rw [PV_RunJoin_NodeSlotRead60.source next0 cc1 cc2 tree queries 0#usize 1#usize 4672#usize
      (PV_RunJoin_NodeSixReads60.read01 base heap box ops)]
    apply PV_RunJoin_ResultBindEq55.complete
    intro status1
    cases status1 with
    | Err e => rfl
    | Ok next1 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      rw [PV_RunJoin_NodeSlotRead60.source next1 cc1 cc2 tree queries 0#usize 2#usize 4096#usize
        (PV_RunJoin_NodeSixReads60.read02 base heap box ops)]
      apply PV_RunJoin_ResultBindEq55.complete
      intro status2
      cases status2 with
      | Err e => rfl
      | Ok next2 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        rw [PV_RunJoin_NodeSlotRead60.source next2 cc1 cc2 tree queries 1#usize 0#usize 5504#usize
          (PV_RunJoin_NodeSixReads60.read10 base heap box ops)]
        apply PV_RunJoin_ResultBindEq55.complete
        intro status3
        cases status3 with
        | Err e => rfl
        | Ok next3 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
          rw [PV_RunJoin_NodeSlotRead60.source next3 cc1 cc2 tree queries 1#usize 1#usize 5504#usize
            (PV_RunJoin_NodeSixReads60.read11 base heap box ops)]
          apply PV_RunJoin_ResultBindEq55.complete
          intro status4
          cases status4 with
          | Err e => rfl
          | Ok next4 =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
            rw [PV_RunJoin_NodeSequence60.singleton]
            exact PV_RunJoin_NodeSlotRead60.source next4 cc1 cc2 tree queries 1#usize 2#usize 4800#usize
              (PV_RunJoin_NodeSixReads60.read12 base heap box ops)

#print axioms source
end R1Z.PV_RunJoin_NodeSixSequence60
