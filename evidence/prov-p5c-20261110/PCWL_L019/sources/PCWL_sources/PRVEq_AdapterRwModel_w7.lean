-- PCWL_ AdapterRwModel require_zero: fresh (frozen 4bb3b3f, slice loop `while !remaining.is_empty()`) = gate (index loop `index < bytes.len()`), all inputs.
-- SOURCE DIFFERENCE (not an encoding difference): the gate's require_zero is an index-based loop; the frozen function loops over `remaining = &remaining[1..]`.
-- Fresh text: PCWL_E001 emission (original Aeneas 959659a6, overflow ON, Charon cargo --jobs 4, identity by class receipt PCWE_E003): require_zero_loop.body, require_zero_loop, require_zero.
-- The gate's require_zero_loop and require_zero_loop.body have no frozen counterpart (different loop state); they are cleared only through the parent equality below.
import Aeneas
import AdapterRwModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AdapterRw
namespace PRVFresh_ARM_w7

/-- [aspis_r1_cost_probe_program::r1_pool_adapter::owned::require_zero]: loop body 0:
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs', lines 74:4-79:1 -/
@[rust_loop_body]
def r1_pool_adapter.owned.require_zero_loop.body
  (remaining : Slice Std.U8) :
  Result (ControlFlow (Slice Std.U8) (core.result.Result Unit
    solana_program_error.ProgramError))
  := do
  let b ← core.slice.Slice.is_empty remaining
  if b
  then ok (done (core.result.Result.Ok ()))
  else
    let i ← Slice.index_usize remaining 0#usize
    if i != 0#u8
    then
      ok (done (core.result.Result.Err
        solana_program_error.ProgramError.AccountAlreadyInitialized))
    else
      let remaining1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) remaining
          { start := 1#usize }
      ok (cont remaining1)

/-- [aspis_r1_cost_probe_program::r1_pool_adapter::owned::require_zero]: loop 0:
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs', lines 74:4-79:1 -/
@[rust_loop]
def r1_pool_adapter.owned.require_zero_loop
  (remaining : Slice Std.U8) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  loop
    (fun remaining1 => r1_pool_adapter.owned.require_zero_loop.body remaining1)
    remaining

/-- [aspis_r1_cost_probe_program::r1_pool_adapter::owned::require_zero]:
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs', lines 73:0-79:1 -/
@[reducible]
def r1_pool_adapter.owned.require_zero
  (remaining : Slice Std.U8) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  r1_pool_adapter.owned.require_zero_loop remaining


end PRVFresh_ARM_w7
end AdapterRw

set_option maxHeartbeats 200000

namespace PRVEq.AdapterRwModel_w7
open AdapterRw

/-- one step of the Aeneas `loop` functional (as in PRVC_LoopBridge) -/
def bs {α β : Type _} (body : α → Result (ControlFlow α β)) (h : α → Result β) (x : α) : Result β :=
  match body x with
  | ok r => match r with
    | ControlFlow.cont x' => h x'
    | ControlFlow.done y => ok y
  | fail e => fail e
  | div => div

theorem loop_unfold {α β : Type _} (body : α → Result (ControlFlow α β)) (x : α) :
    loop body x = bs body (loop body) x := by
  rw [loop]; rfl
#print axioms loop_unfold

/-- the pure specification: Ok iff every byte is zero, otherwise AccountAlreadyInitialized -/
def zs : List Std.U8 → core.result.Result Unit solana_program_error.ProgramError
  | [] => core.result.Result.Ok ()
  | b :: t => if (b != 0#u8) = true then core.result.Result.Err solana_program_error.ProgramError.AccountAlreadyInitialized else zs t

theorem fresh_loop (l : List Std.U8) : ∀ s : Slice Std.U8, s.val = l →
    PRVFresh_ARM_w7.r1_pool_adapter.owned.require_zero_loop s = ok (zs l) := by
  induction l with
  | nil =>
    intro s hs
    unfold PRVFresh_ARM_w7.r1_pool_adapter.owned.require_zero_loop
    rw [loop_unfold]
    simp [bs, PRVFresh_ARM_w7.r1_pool_adapter.owned.require_zero_loop.body, core.slice.Slice.is_empty, Slice.length, hs, zs]
  | cons b t ih =>
    intro s hs
    unfold PRVFresh_ARM_w7.r1_pool_adapter.owned.require_zero_loop
    have h0 : Slice.index_usize s 0#usize = ok b := by
      simp [Slice.index_usize, hs]
    obtain ⟨s', hs', hv⟩ : ∃ s' : Slice Std.U8, core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) s { start := 1#usize } = ok s' ∧ s'.val = t := by
      refine ⟨s.drop 1#usize, ?_, ?_⟩ <;>
        simp [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice, core.slice.index.SliceIndexRangeFromUsizeSlice.index, Slice.drop, hs, Slice.length]
    rw [loop_unfold]
    by_cases hb0 : b = 0#u8
    · simp [bs, PRVFresh_ARM_w7.r1_pool_adapter.owned.require_zero_loop.body, core.slice.Slice.is_empty, Slice.length, hs, h0, hb0, hs', zs]
      exact ih s' hv
    · simp [bs, PRVFresh_ARM_w7.r1_pool_adapter.owned.require_zero_loop.body, core.slice.Slice.is_empty, Slice.length, hs, h0, hb0, zs]
#print axioms fresh_loop

end PRVEq.AdapterRwModel_w7
