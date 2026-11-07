import NMT_345ZeroAll
import NMT_345CheckpointData
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result

theorem zero_source (bytes : Slice U8) :
 AdapterRw.r1_pool_adapter.owned.require_zero bytes =
 .ok (if bytes.val.all (· == 0#u8) then .Ok () else .Err .AccountAlreadyInitialized) := by
 unfold AdapterRw.r1_pool_adapter.owned.require_zero
 rw [zero_all_loop bytes bytes.val.length 0#usize (by change 0 + bytes.val.length = bytes.val.length; omega)]
 simp only [show (0#usize).val = 0 from rfl,List.drop_zero]
 cases h : bytes.val.all (· == 0#u8) <;> rfl

def zeroCall (bytes : Slice U8) : Result (core.result.Result Unit PE) :=
 mapOuter (mapCore id fromPE) (AdapterRw.r1_pool_adapter.owned.require_zero bytes)
/-- Existing CLOSED342 on its exact own-argument bound. -/
theorem zero_closed (bytes : Slice U8) (bound : bytes.val.length ≤ 4096) :
 zeroCall bytes = mapOuter (mapCore id fromPE)
  (do let b ← NFQ_ScanReference.zero_ref bytes; .ok (NFQ_ZeroSource.result b)) := by
 unfold zeroCall
 rw [NFU_ZeroPort.source bytes bound]

theorem zero_value (bytes : Slice U8) : zeroCall bytes =
 .ok (if bytes.val.all (· == 0#u8) then .Ok () else .Err .AccountAlreadyInitialized) := by
 unfold zeroCall
 rw [zero_source]
 cases bytes.val.all (· == 0#u8) <;> rfl

def zeroStep {W : Type} (s : CheckpointData W) (next : CheckpointData W → Result Ret) : Result Ret :=
 tryStep (zeroCall s.checkpointData) (fun _ => next s)
theorem zeroStep_value {W : Type} (s : CheckpointData W) (next : CheckpointData W → Result Ret) :
 zeroStep s next = if s.checkpointData.val.all (· == 0#u8) then next s else .ok (.Err .AccountAlreadyInitialized) := by
 unfold zeroStep
 rw [zero_value]
 split <;> rfl
#print axioms zero_source
#print axioms zero_closed
#print axioms zero_value
#print axioms zeroStep_value
end NMT_345
