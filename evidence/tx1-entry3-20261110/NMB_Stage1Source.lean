import NMB_SnapshotReplay
import NLD_Stage1Source
import NLQ_CopyTrace
set_option autoImplicit false
noncomputable section
namespace NMB_Stage1Source
open Aeneas Aeneas.Std Result AspisR1
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Bytes := alloc.vec.Vec U8
/-- One parent state. SDK cells retain account-occurrence metadata; checkpoint
and snapshot buffers remain owned until the exact source cleanup occurrence. -/
structure State where
 snapshots : NMB_Snapshot.State
 checkpoint : Option Bytes := none
inductive Event where
 | snapshot (event : NMB_Snapshot.Event)
 | owned (before after : State) (program : Key) (accounts : Slice NMB_Input.Owned)
   (instruction : Slice U8) (reply : Result (core.result.Result Bytes PE))
   (sourceOccurrences : List Nat)
 | copy (event : NLQ_CopyTrace.Event)
 | cleanup (before after : State)
structure Run where
 result : Result (core.result.Result Unit PE)
 post : State
 events : List Event
/-- The existing full copy/SDK token model is reused unchanged. -/
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
/-- Full emitted-source erasure is NLD's, reused line-faithfully. Free Ops
here are intermediate SOURCE parameters; this declaration is never a row root. -/
def continuation (ops : AdapterRw.Ops) (p : Key) (d : Slice U8) (accounts : Slice NMB_Input.Owned) (s : State) : Run :=
 let child := NLD_Stage1Source.stage1Owned ops p accounts d
 let event := Event.owned s s p accounts d child.2 child.1
 match child.2 with
 | .fail e => ⟨.fail e,s,[event]⟩
 | .div => ⟨.div,s,[event]⟩
 | .ok (.Err e) =>
   let after := {s with snapshots:={s.snapshots with owned:=[]}}
   ⟨.ok (.Err e),after,[event,.cleanup s after]⟩
 | .ok (.Ok saved) =>
   let copied := copyResult s saved
   {copied with events:=event::copied.events}
def G (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (alloc0 alloc1 alloc2 : Result Unit) : Run :=
 let snapshots := NMB_ThreeSnapshots.G x alloc0 alloc1 alloc2
 let events := snapshots.events.map Event.snapshot
 match snapshots.result with
 | .fail err => ⟨.fail err,⟨NMB_SnapshotReplay.replay (NMB_Snapshot.ready x 0 []) snapshots.events,none⟩,events⟩
 | .div => ⟨.div,⟨NMB_SnapshotReplay.replay (NMB_Snapshot.ready x 0 []) snapshots.events,none⟩,events⟩
 | .ok (accounts,post) =>
   let tail := continuation ops p d accounts ⟨post,none⟩
   {tail with events:=events++tail.events}
#print State
#print G
end NMB_Stage1Source
