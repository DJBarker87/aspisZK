import NNH_NativeOracleAbort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_NativeOracleBatch
open Aeneas Aeneas.Std Result NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NNH_NativeOracleSlots
variable (H : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)

theorem calls (proof : Slice U8) (raw : Array U32 22#usize) (batch : Usize)
 (sites : List NLL_Parent.Call) (idx : NLL.Indices) (val : NLL.Values)
 (history : NLL.History) (out : NLL.Reply)
 (native : NLL_Parent.Calls (part H pda clock r) proof raw batch sites idx val history out) :
 NLL_Parent.Calls H proof raw batch sites idx val history out := by
 induction native with
 | nil idx val => exact .nil idx val
 | error root kind rest idx nextIdx val nextVal events error child =>
  exact .error root kind rest idx nextIdx val nextVal events error
   (NNH_NativeOracleLoop.invocation H pda clock r _ _ _ _ _ _ _ _ _ child)
 | next root kind rest idx nextIdx val nextVal events history out child tail ih =>
  exact .next root kind rest idx nextIdx val nextVal events history out
   (NNH_NativeOracleLoop.invocation H pda clock r _ _ _ _ _ _ _ _ _ child) ih

theorem abortCalls (proof : Slice U8) (raw : Array U32 22#usize) (batch : Usize)
 (sites : List NLL_Parent.Call) (idx : NLL.Indices) (val : NLL.Values)
 (history : NLL.History) (pending : NLL.Pending)
 (native : NLL_Parent.AbortCalls (part H pda clock r) proof raw batch sites idx val history pending) :
 NLL_Parent.AbortCalls H proof raw batch sites idx val history pending := by
 induction native with
 | here root kind rest idx val events pending child =>
  exact .here root kind rest idx val events pending
   (NNH_NativeOracleAbort.invocation H pda clock r _ _ _ _ _ _ _ _ _ child)
 | next root kind rest idx nextIdx val nextVal events history pending child tail ih =>
  exact .next root kind rest idx nextIdx val nextVal events history pending
   (NNH_NativeOracleLoop.invocation H pda clock r _ _ _ _ _ _ _ _ _ child) ih

theorem returning (proof : Slice U8) (p : AspisR1Stage2.verifier.Prepared)
 (folded : NLL.Root) (batch : Usize) (history : NLL.History) (out : NLL.Reply)
 (native : NLL_BatchSource.Invocation (part H pda clock r) proof p folded batch history out) :
 NLL_BatchSource.Invocation H proof p folded batch history out :=
 calls H pda clock r _ _ _ _ _ _ _ _ native

theorem aborting (proof : Slice U8) (p : AspisR1Stage2.verifier.Prepared)
 (folded : NLL.Root) (batch : Usize) (history : NLL.History) (pending : NLL.Pending)
 (native : NLL_BatchAbort.Invocation (part H pda clock r) proof p folded batch history pending) :
 NLL_BatchAbort.Invocation H proof p folded batch history pending :=
 abortCalls H pda clock r _ _ _ _ _ _ _ _ native
#print axioms calls
#print axioms abortCalls
#print axioms returning
#print axioms aborting
end AspisR1.NNH_NativeOracleBatch
end
