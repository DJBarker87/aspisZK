import NLQ_Stage1Copy
import NLD_Stage1Source
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1State
open Aeneas Aeneas.Std Result AspisR1
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Owned := AdapterRw.r1_pool_adapter.owned.OwnedAccount
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Bytes := alloc.vec.Vec U8
/-- One state for stage1 after source-order snapshots. Account/cell identity,
full payloads, and token allocator are retained, together with owned carriers. -/
structure State where
 snapshots : NLM_Snapshot.State
 checkpoint : Option Bytes := none
/-- Every occurrence has SAME before/after state, complete return and its full
child event prefix. These are model events until native cuts are installed. -/
inductive Event where
 | snapshot (event : NLM_Snapshot.Event)
 | owned (before after : State) (program : Key) (accounts : Slice Owned)
   (instruction : Slice U8) (reply : Result (core.result.Result Bytes PE))
   (sourceOccurrences : List Nat)
 | copy (event : NLQ_CopyTrace.Event)
 | cleanup (before after : State)
structure Run where
 result : Result (core.result.Result Unit PE)
 post : State
 events : List Event
/-- SDK aborts have no guard-drop/owned-cleanup suffix. -/
def copyResult (s : State) (saved : Bytes) : Run :=
 let copied := NLQ_CopyTrace.G s.snapshots.sdk 2 s.snapshots.next
   (S2W_ReturnedCheckpoint.nativeBytes saved)
 match copied.outcome with
 | .returned sdk reply =>
   let before := {s with snapshots:={s.snapshots with sdk:=sdk},checkpoint:=some saved}
   let after := {before with snapshots:={before.snapshots with owned:=[]},checkpoint:=none}
   let result := match reply with
     | .ok _ => core.result.Result.Ok ()
     | .error _ => core.result.Result.Err AdapterRw.solana_program_error.ProgramError.AccountBorrowFailed
   ⟨.ok result,after,copied.events.map Event.copy++[.cleanup before after]⟩
 | .abort sdk =>
   ⟨.fail .panic,{s with snapshots:={s.snapshots with sdk:=sdk},checkpoint:=some saved},
    copied.events.map Event.copy⟩
/-- Complete Result of the OWNED child at the actual owned array and original
instruction. No selected-success assumption or independent post is supplied. -/
def continuation (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) (s : State) : Run :=
 let child := AspisR1.NLD_Stage1Source.stage1Owned ops p s.snapshots.input.first d
 let event := Event.owned s s p s.snapshots.input.first d child.2 child.1
 match child.2 with
 | .fail e => ⟨.fail e,s,[event]⟩
 | .div => ⟨.div,s,[event]⟩
 | .ok (.Err error) =>
   let after := {s with snapshots:={s.snapshots with owned:=[]}}
   ⟨.ok (.Err error),after,[event,.cleanup s after]⟩
 | .ok (.Ok saved) =>
   let copied := copyResult s saved
   {copied with events:=event::copied.events}
#print State
#print Event
#print continuation
end NLQ_Stage1State
