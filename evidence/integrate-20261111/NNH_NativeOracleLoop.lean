import NNH_NativeOracleSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_NativeOracleLoop
open Aeneas Aeneas.Std Result MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NNH_NativeOracleSlots
variable (H : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)

theorem terminal (root : NLL.Root) (batch kind : Nat) (nodes : Slice U8)
 (scratch : reference.Scratch) (events : List NLL.Event) (out : NLL.Answer)
 (native : NLL.Terminal (part H pda clock r) root batch kind nodes scratch events out) :
 NLL.Terminal H root batch kind nodes scratch events out := by
 cases native with
 | missing bad => exact .missing bad
 | capacity well excess => exact .capacity well excess
 | padding well fits bad => exact .padding well fits bad
 | verify well fits padding queries out child =>
  apply NLL.Terminal.verify well fits padding queries out
  have same := funext (node H pda clock r)
  rw [same] at child
  exact child

theorem loop (proof : Slice U8) (root : NLL.Root) (batch : Nat) (kind lo n slot : Usize)
 (f : NLL.Frame) (events : List NLL.Event) (out : NLL.Answer)
 (native : NLL.Loop (part H pda clock r) proof root batch kind lo n slot f events out) :
 NLL.Loop H proof root batch kind lo n slot f events out := by
 induction native with
 | reject f more step =>
  rw [NNH_NativeOracleSlots.event H pda clock r]
  rw [NNH_NativeOracleSlots.digest H pda clock r] at step
  exact .reject f more step
 | next f t more step events out tail ih =>
  rw [NNH_NativeOracleSlots.event H pda clock r]
  rw [NNH_NativeOracleSlots.digest H pda clock r] at step
  exact .next f t more step events out ih
 | terminal f done events out tail =>
  have same := terminal H pda clock r root batch kind.val _ f.scratch events out tail
  rw [nodeView (part H pda clock r) H] at same
  exact .terminal f done events out same

theorem invocation (proof : Slice U8) (raw : Array U32 22#usize) (root : NLL.Root)
 (batch kind : Usize) (idx : NLL.Indices) (val : NLL.Values)
 (events : List NLL.Event) (out : NLL.Answer)
 (native : NLL.Invocation (part H pda clock r) proof raw root batch kind idx val events out) :
 NLL.Invocation H proof raw root batch kind idx val events out := by
 obtain ⟨rest,events,body⟩ := native
 rw [entryKeys (part H pda clock r) H] at events body
 exact ⟨rest,events,loop H pda clock r _ _ _ _ _ _ _ _ _ _ body⟩
#print axioms terminal
#print axioms loop
#print axioms invocation
end AspisR1.NNH_NativeOracleLoop
end
