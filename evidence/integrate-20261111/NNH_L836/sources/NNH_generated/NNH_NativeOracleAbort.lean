import NNH_NativeOracleLoop
import NLL_ParentAbortInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_NativeOracleAbort
open Aeneas Aeneas.Std Result MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NNH_NativeOracleSlots
variable (H : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)

theorem loop (proof : Slice U8) (root : NLL.Root) (batch : Nat) (kind lo n slot : Usize)
 (f : NLL.Frame) (events : List NLL.Event) (pending : NLL.Pending)
 (native : NLL.AbortLoop (part H pda clock r) proof root batch kind lo n slot f events pending) :
 NLL.AbortLoop H proof root batch kind lo n slot f events pending := by
 induction native with
 | leaf f more =>
  rw [view (part H pda clock r) H]
  exact .leaf f more
 | verify f done well fits padding queries q pending child =>
  rw [nodeView (part H pda clock r) H] at padding child
  apply NLL.AbortLoop.verify f done well fits padding queries q pending
  have same := funext (node H pda clock r)
  rw [same] at child
  exact child
 | next f t more step events pending tail ih =>
  rw [NNH_NativeOracleSlots.event H pda clock r]
  rw [NNH_NativeOracleSlots.digest H pda clock r] at step
  exact .next f t more step events pending ih

theorem invocation (proof : Slice U8) (raw : Array U32 22#usize) (root : NLL.Root)
 (batch kind : Usize) (idx : NLL.Indices) (val : NLL.Values)
 (events : List NLL.Event) (pending : NLL.Pending)
 (native : NLL.AbortInvocation (part H pda clock r) proof raw root batch kind idx val events pending) :
 NLL.AbortInvocation H proof raw root batch kind idx val events pending := by
 obtain ⟨rest,events,body⟩ := native
 rw [entryKeys (part H pda clock r) H] at events body
 exact ⟨rest,events,loop H pda clock r _ _ _ _ _ _ _ _ _ _ body⟩
#print axioms loop
#print axioms invocation
end AspisR1.NNH_NativeOracleAbort
end
