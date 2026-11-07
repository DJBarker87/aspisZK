import NMX_R3_LaneTry
set_option autoImplicit false
namespace NMX_R3_LaneQuestionCuts
open Aeneas Aeneas.Std Result

theorem frontier (b : Slice U8) (master : Array U8 32#usize) (laneId : U8)
 (t : Slice U8) (next : U64) (root : Array U32 8#usize) :
 NMX_R3_LaneCuts.frontier b master laneId t next root =
 NMX_R3_LaneTry.question (NCV_Reference.decode_frontier t next)
  (fun f => NMX_R3_LaneCuts.finish b master laneId next root f) := by
 unfold NMX_R3_LaneCuts.frontier NMX_R3_LaneTry.question
 apply congrArg (fun k => (NCV_Reference.decode_frontier t next >>= k))
 funext r
 cases r with
 | Ok a => rfl
 | Err u => cases u; rfl

theorem digest (b : Slice U8) (master : Array U8 32#usize) (laneId : U8)
 (t : Slice U8) (next : U64) :
 NMX_R3_LaneCuts.digest b master laneId t next =
 NMX_R3_LaneTry.question (NCV_Reference.digest t 16#usize)
  (fun r => NMX_R3_LaneCuts.frontier b master laneId t next r) := by
 unfold NMX_R3_LaneCuts.digest NMX_R3_LaneTry.question
 apply congrArg (fun k => (NCV_Reference.digest t 16#usize >>= k))
 funext r
 cases r with
 | Ok a => rfl
 | Err u => cases u; rfl

theorem frontier_map (r : core.result.Result (Array (Array U32 8#usize) 20#usize) Unit) :
 NMX_R3_LaneTry.option (fun (f : Array (Array U32 8#usize) 20#usize) =>
  f.val.map (fun (row : Array U32 8#usize) => row.val.map NMX_R3_ByteCarrier.word)) r =
 NMX_R3_FrontierBridge.result r := by
 cases r with
 | Ok a => rfl
 | Err u => cases u; rfl

theorem digest_map (r : core.result.Result (Array U32 8#usize) Unit) :
 NMX_R3_LaneTry.option (fun (a : Array U32 8#usize) => a.val.map NMX_R3_ByteCarrier.word) r =
 NMX_R3_DigestBridge.result r := by
 cases r with
 | Ok a => rfl
 | Err u => cases u; rfl
theorem option_bind {A B : Type} (m : Option A) (f : A → Option B) :
 m.bind f = (match m with | none => none | some a => f a) := by
 cases m <;> rfl
#print axioms option_bind

#print axioms frontier_map
#print axioms digest_map

#print axioms frontier
#print axioms digest
end NMX_R3_LaneQuestionCuts
