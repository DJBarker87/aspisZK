import R1Z.PV_RunJoin_NodeSlotRead60
import R1Z.PV_RunJoin_NodeCaps60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NodeSixReads60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem read00 (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_NodeSlotRead60.Read (types base) (selected base heap box ops) 0#usize 0#usize 4672#usize := by
  unfold PV_RunJoin_NodeSlotRead60.Read
  rw [PV_RunJoin_NodeCaps60.installed base heap box ops]
  rfl
#print axioms read00

theorem read01 (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_NodeSlotRead60.Read (types base) (selected base heap box ops) 0#usize 1#usize 4672#usize := by
  unfold PV_RunJoin_NodeSlotRead60.Read
  rw [PV_RunJoin_NodeCaps60.installed base heap box ops]
  rfl
#print axioms read01

theorem read02 (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_NodeSlotRead60.Read (types base) (selected base heap box ops) 0#usize 2#usize 4096#usize := by
  unfold PV_RunJoin_NodeSlotRead60.Read
  rw [PV_RunJoin_NodeCaps60.installed base heap box ops]
  rfl
#print axioms read02

theorem read10 (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_NodeSlotRead60.Read (types base) (selected base heap box ops) 1#usize 0#usize 5504#usize := by
  unfold PV_RunJoin_NodeSlotRead60.Read
  rw [PV_RunJoin_NodeCaps60.installed base heap box ops]
  rfl
#print axioms read10

theorem read11 (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_NodeSlotRead60.Read (types base) (selected base heap box ops) 1#usize 1#usize 5504#usize := by
  unfold PV_RunJoin_NodeSlotRead60.Read
  rw [PV_RunJoin_NodeCaps60.installed base heap box ops]
  rfl
#print axioms read11

theorem read12 (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @PV_RunJoin_NodeSlotRead60.Read (types base) (selected base heap box ops) 1#usize 2#usize 4800#usize := by
  unfold PV_RunJoin_NodeSlotRead60.Read
  rw [PV_RunJoin_NodeCaps60.installed base heap box ops]
  rfl
#print axioms read12

end R1Z.PV_RunJoin_NodeSixReads60
