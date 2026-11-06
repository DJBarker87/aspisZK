import NLE_WrapperState
set_option autoImplicit false
noncomputable section
namespace NLE_Wrapper
open Aeneas Aeneas.Std Result
/-- Frozen stage2 source order: guard, clear, seven snapshots, Clock, owned.
Clock is called even when a snapshot contains a deferred inner error. -/
def G {Account : Type} (ops : Ops Account) (state : State Account) : Run Account PR := do
 let allowed ← NJU_Log.record (.header state) (ops.header state.frame.accounts state.frame.data)
 if !allowed then pure (.Err .InvalidInstructionData) else do
 let _ ← clear ops state
 let (a0,s0) ← snapshot ops state 0#usize 58295#usize 58295#usize
 let (a1,s1) ← snapshot ops s0 1#usize 384#usize 384#usize
 let (a2,s2) ← snapshot ops s1 2#usize 192#usize 192#usize
 let (a3,s3) ← snapshot ops s2 3#usize 768#usize 768#usize
 let (a4,s4) ← snapshot ops s3 4#usize 128#usize 256#usize
 let (a5,s5) ← snapshot ops s4 5#usize 192#usize 320#usize
 let (a6,s6) ← snapshot ops s5 6#usize 1768#usize 1768#usize
 let slot ← NJU_Log.record (.clock s6) ops.clock
 let post := {s6 with slot := some slot}
 let owned := Array.make 7#usize [a0,a1,a2,a3,a4,a5,a6]
 NJU_Log.record (.child post owned slot)
  (ops.child state.frame.program owned.to_slice state.frame.data slot)
/-- Whole source transcription (SDK wrapper has no AdapterRwModel declaration).
Native stage cuts still have to justify this transcription at the ABI. -/
def source {Account : Type} (ops : Ops Account) (state : State Account) : Result PR := do
 let allowed ← ops.header state.frame.accounts state.frame.data
 if !allowed then pure (.Err .InvalidInstructionData) else do
 let empty : Slice U8 := ⟨[],by simp⟩
 let _ ← ops.clear empty
 let a0 ← state.frame.accounts.index_usize 0#usize
 let a0 ← ops.snapshot a0 58295#usize 58295#usize
 let a1 ← state.frame.accounts.index_usize 1#usize
 let a1 ← ops.snapshot a1 384#usize 384#usize
 let a2 ← state.frame.accounts.index_usize 2#usize
 let a2 ← ops.snapshot a2 192#usize 192#usize
 let a3 ← state.frame.accounts.index_usize 3#usize
 let a3 ← ops.snapshot a3 768#usize 768#usize
 let a4 ← state.frame.accounts.index_usize 4#usize
 let a4 ← ops.snapshot a4 128#usize 256#usize
 let a5 ← state.frame.accounts.index_usize 5#usize
 let a5 ← ops.snapshot a5 192#usize 320#usize
 let a6 ← state.frame.accounts.index_usize 6#usize
 let a6 ← ops.snapshot a6 1768#usize 1768#usize
 let slot ← ops.clock
 ops.child state.frame.program (Array.make 7#usize [a0,a1,a2,a3,a4,a5,a6]).to_slice state.frame.data slot
end NLE_Wrapper
