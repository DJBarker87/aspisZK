import R1Z.PV_RunJoin_NodeSlotRead60
import R1Z.PV_RunJoin_NodeCaps60
import R1Z.PV_RunJoin_LayoutArithmetic41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NodeSixReads60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem read00 (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_NodeSlotRead60.Read (types base) (selected base heap box ops) 0#usize 0#usize 4672#usize := by
  unfold PV_RunJoin_NodeSlotRead60.Read
  rw [PV_RunJoin_NodeCaps60.installed base heap box ops]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_LayoutArithmetic41.mul 3#usize 0#usize 0#usize rfl,
    PV_RunJoin_LayoutArithmetic41.add 0#usize 0#usize 0#usize rfl]
  have hi : Array.index_usize ProverRwDictionaryLayoutSource.compact.SLOT_NODES 0#usize=ok 146#usize := rfl
  rw [hi]
  simp only [bind_tc_ok]
  exact congrArg Result.ok (PV_RunJoin_LayoutArithmetic41.mul 32#usize 146#usize 4672#usize rfl)
#print axioms read00

theorem read01 (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_NodeSlotRead60.Read (types base) (selected base heap box ops) 0#usize 1#usize 4672#usize := by
  unfold PV_RunJoin_NodeSlotRead60.Read
  rw [PV_RunJoin_NodeCaps60.installed base heap box ops]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_LayoutArithmetic41.mul 3#usize 0#usize 0#usize rfl,
    PV_RunJoin_LayoutArithmetic41.add 0#usize 1#usize 1#usize rfl]
  have hi : Array.index_usize ProverRwDictionaryLayoutSource.compact.SLOT_NODES 1#usize=ok 146#usize := rfl
  rw [hi]
  simp only [bind_tc_ok]
  exact congrArg Result.ok (PV_RunJoin_LayoutArithmetic41.mul 32#usize 146#usize 4672#usize rfl)
#print axioms read01

theorem read02 (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_NodeSlotRead60.Read (types base) (selected base heap box ops) 0#usize 2#usize 4096#usize := by
  unfold PV_RunJoin_NodeSlotRead60.Read
  rw [PV_RunJoin_NodeCaps60.installed base heap box ops]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_LayoutArithmetic41.mul 3#usize 0#usize 0#usize rfl,
    PV_RunJoin_LayoutArithmetic41.add 0#usize 2#usize 2#usize rfl]
  have hi : Array.index_usize ProverRwDictionaryLayoutSource.compact.SLOT_NODES 2#usize=ok 128#usize := rfl
  rw [hi]
  simp only [bind_tc_ok]
  exact congrArg Result.ok (PV_RunJoin_LayoutArithmetic41.mul 32#usize 128#usize 4096#usize rfl)
#print axioms read02

theorem read10 (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_NodeSlotRead60.Read (types base) (selected base heap box ops) 1#usize 0#usize 5504#usize := by
  unfold PV_RunJoin_NodeSlotRead60.Read
  rw [PV_RunJoin_NodeCaps60.installed base heap box ops]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_LayoutArithmetic41.mul 3#usize 1#usize 3#usize rfl,
    PV_RunJoin_LayoutArithmetic41.add 3#usize 0#usize 3#usize rfl]
  have hi : Array.index_usize ProverRwDictionaryLayoutSource.compact.SLOT_NODES 3#usize=ok 172#usize := rfl
  rw [hi]
  simp only [bind_tc_ok]
  exact congrArg Result.ok (PV_RunJoin_LayoutArithmetic41.mul 32#usize 172#usize 5504#usize (by change 32*172=5504; norm_num))
#print axioms read10

theorem read11 (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_NodeSlotRead60.Read (types base) (selected base heap box ops) 1#usize 1#usize 5504#usize := by
  unfold PV_RunJoin_NodeSlotRead60.Read
  rw [PV_RunJoin_NodeCaps60.installed base heap box ops]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_LayoutArithmetic41.mul 3#usize 1#usize 3#usize rfl,
    PV_RunJoin_LayoutArithmetic41.add 3#usize 1#usize 4#usize rfl]
  have hi : Array.index_usize ProverRwDictionaryLayoutSource.compact.SLOT_NODES 4#usize=ok 172#usize := rfl
  rw [hi]
  simp only [bind_tc_ok]
  exact congrArg Result.ok (PV_RunJoin_LayoutArithmetic41.mul 32#usize 172#usize 5504#usize (by change 32*172=5504; norm_num))
#print axioms read11

theorem read12 (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_NodeSlotRead60.Read (types base) (selected base heap box ops) 1#usize 2#usize 4800#usize := by
  unfold PV_RunJoin_NodeSlotRead60.Read
  rw [PV_RunJoin_NodeCaps60.installed base heap box ops]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_LayoutArithmetic41.mul 3#usize 1#usize 3#usize rfl,
    PV_RunJoin_LayoutArithmetic41.add 3#usize 2#usize 5#usize rfl]
  have hi : Array.index_usize ProverRwDictionaryLayoutSource.compact.SLOT_NODES 5#usize=ok 150#usize := rfl
  rw [hi]
  simp only [bind_tc_ok]
  exact congrArg Result.ok (PV_RunJoin_LayoutArithmetic41.mul 32#usize 150#usize 4800#usize rfl)
#print axioms read12

end R1Z.PV_RunJoin_NodeSixReads60
