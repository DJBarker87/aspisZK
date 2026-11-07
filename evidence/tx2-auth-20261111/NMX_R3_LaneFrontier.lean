import NMX_R3_LaneFinish
import NMX_R3_LaneQuestionCuts
set_option autoImplicit false
namespace NMX_R3_LaneFrontier
open Aeneas Aeneas.Std Result RSL NMX_R3_ByteCarrier NMX_R3_LaneCarrier NMX_R3_LaneObserve
attribute [local irreducible] RSL.TX2_217.frontierLoop NCV_Reference.decode_frontier

theorem value (b : Slice U8) (master : Array U8 32#usize) (laneId : U8)
 (t : Slice U8) (next : U64) (root : Array U32 8#usize)
 (bExtent : b.val.length = 768) (tExtent : t.val.length = 688) :
 observe (NMX_R3_LaneCuts.frontier b master laneId t next root) =
 ok (NMX_R3_LaneModels.frontier (b.val.map byte) (key master) (byte laneId)
  (t.val.map byte) (long next) (root.val.map word)) := by
 obtain ⟨r,call,mapped⟩ := NMX_R3_FrontierBridge.value t next (by omega) (by omega)
 rw [NMX_R3_LaneQuestionCuts.frontier]
 have joined := NMX_R3_LaneTry.fold (NCV_Reference.decode_frontier t next) r
  (fun (f : Array (Array U32 8#usize) 20#usize) => f.val.map (fun (row : Array U32 8#usize) => row.val.map word))
  (TX2_217.frontierLoop (t.val.map byte) (long next) 20)
  (fun f => NMX_R3_LaneCuts.finish b master laneId next root f)
  (NMX_R3_LaneModels.emit (b.val.map byte) (key master) (byte laneId) (long next) (root.val.map word))
  call ((NMX_R3_LaneQuestionCuts.frontier_map r).trans mapped) (fun f => NMX_R3_LaneFinish.value b master laneId next root f bExtent)
 rw [joined]
 unfold NMX_R3_LaneModels.frontier
 simp only [TREE_DEPTH]
 generalize TX2_217.frontierLoop (t.val.map byte) (long next) 20 = model
 cases model <;> rfl

#print axioms value
end NMX_R3_LaneFrontier
