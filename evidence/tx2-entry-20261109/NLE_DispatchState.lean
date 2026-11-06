import NJD_EntrySpine
set_option autoImplicit false
noncomputable section
namespace NLE_Dispatch
open Aeneas Aeneas.Std Result AspisR1
abbrev Key := Hiq_DispatchSource.Key
abbrev PE := Hiq_DispatchSource.PE
abbrev PR := core.result.Result Unit PE
structure State (Account : Type) where
 program : Key
 accounts : Slice Account
 data : Slice U8
 head : Option (Option U8) := none
 selected : Option Nat := none
abbrev Event (Account : Type) := NJD_EntrySpine.Event Account
abbrev Run (Account A : Type) := NJD_Trace.Run (Event Account) A
/-- One state and one source-ordered event family; actual head/copy/equality
windows are reused from NJD, preserving all Err/fail/div branches. -/
def G {Account : Type} (ops : NIV_RawBoundary.Boundaries Account)
 (state : State Account) : Run Account PR :=
 NJD_Trace.bind (NJD_Trace.call (.head state.data) (ops.head state.data)) fun head =>
 let post := {state with head := some head}
 NJD_Trace.bind (NJD_Trace.call (.copied head) (ops.copy head)) fun value =>
 NJD_EntrySpine.dispatch ops post.program post.accounts post.data value
end NLE_Dispatch
