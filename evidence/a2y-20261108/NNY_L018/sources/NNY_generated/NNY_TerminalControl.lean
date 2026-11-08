import NNY_MerkleTerminalFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_TerminalControl
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeBatchBody NKV_StepErasure NKV_LoopTransport
/-- The terminal source branch has no continuation, for any operation replies. -/
theorem no_cont (base : Ops) (D : aspis_core.digest.Digest32 Unit)
 (proof : Slice U8) (root : Array U8 32#usize) (slot d : Usize)
 (idx : Indices) (val : Values) (next : State) :
 NNY_MerkleTerminalFrame.code base D proof root () slot d idx val ≠ ok (.cont next) := by
 intro read
 unfold NNY_MerkleTerminalFrame.code at read
 repeat' first
 | (solve | cases read)
 | uncase_result
 | head_reduce read
 | split at read
#print axioms no_cont
end AspisR1.NNY_TerminalControl
end
