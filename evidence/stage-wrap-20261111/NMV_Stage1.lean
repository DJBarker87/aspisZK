import NMV_Model
set_option autoImplicit false
namespace NMV_Stage1
open NMV_Model NMV_Snapshot

def admitted (a : Args) : Bool :=
 decide ((a.data = [3,10] ∨ a.data = [3,11]) ∧ a.accounts.length=3)

def plan (a : Args) : List (Nat × Nat × Nat) :=
 [(a.accounts[0]?.getD 0,58295,58295),
  (a.accounts[1]?.getD 0,1880,1880),
  (a.accounts[2]?.getD 0,1768,1768)]

def before (a : Args) : World × ChildArgs :=
 let r := snapshots a.world.sdk (plan a)
 (⟨r.1,a.world.runtime  ++ 
     ((r.1.events.drop a.world.sdk.events.length).map RuntimeEvent.sdk)⟩,⟨a.program,r.2,a.data,none⟩)

/-- Explicit SDK token pre in lexical source order. The abort case ends
at the failed length check; no guard cleanup or post-abort state is invented. -/
def copyEvents (w : World) (account : Nat) (checkpoint : Bytes) : List NLF_ParentModel.Event :=
 let r := NLF_SdkModel.try_borrow_mut_data w.sdk.state account w.sdk.next
 let acquire := NLF_ParentModel.Event.acquire account w.sdk.next .exclusive r.2
 match r.2 with
 | .error _ => [acquire]
 | .ok g =>
   let p := NLF_SdkModel.deref r.1 g
   if checkpoint.length=p.bytes.length then
     [acquire,.deref g (.ok p),.release g (.ok ())]
   else [acquire,.deref g (.ok p)]

def copyRuntime (w : World) (account : Nat) (checkpoint : Bytes) : List RuntimeEvent :=
 let es := copyEvents w account checkpoint
 if es.length=3 then
   (es.take 2).map RuntimeEvent.sdk  ++  [.checkpointWrite account checkpoint]  ++ 
     (es.drop 2).map RuntimeEvent.sdk
 else es.map RuntimeEvent.sdk

/-- NLF's KMX value induction covers all bytes. No world is exposed after abort. -/
def writeCheckpoint (w : World) (account : Nat) (checkpoint : Bytes) : End Unit :=
 let events := copyEvents w account checkpoint
 let trace := w.runtime  ++  copyRuntime w account checkpoint
 match NLF_CopyStep.run w.sdk.state account w.sdk.next checkpoint with
 | .returned s result =>
   let reply : Except PE Unit := match result with
     | .ok _ => .ok ()
     | .error _ => .error .AccountBorrowFailed
   .returned
     { w with
       sdk := { w.sdk with state := s, next := w.sdk.next+1, events := w.sdk.events ++ events }
       runtime := trace } reply
 | .abort _ => .stopped (w.sdk.events ++ events) trace

def finish (w : World) (account : Nat) (child : ChildEnd Bytes) : End Unit :=
 match child with
 | .stopped pre => .stopped w.sdk.events (w.runtime ++ pre)
 | .returned (.error e) suffix => .returned {w with runtime := w.runtime ++ suffix} (.error e)
 | .returned (.ok checkpoint) suffix =>
   writeCheckpoint {w with runtime := w.runtime ++ suffix} account checkpoint

def run (a : Args) (child : ChildEnd Bytes) : Option ChildArgs × End Unit :=
 if admitted a then
   let b := before a
   (some b.2,finish b.1 (a.accounts[2]?.getD 0) child)
 else (none,.returned a.world (.error .InvalidInstructionData))

theorem rejection (a : Args) (child : ChildEnd Bytes) (h : admitted a = false) :
 run a child = (none,.returned a.world (.error .InvalidInstructionData)) := by
 simp only [run,h,Bool.false_eq_true,if_false]

theorem entered (a : Args) (child : ChildEnd Bytes) (h : admitted a = true) :
 run a child = (some (before a).2,finish (before a).1 (a.accounts[2]?.getD 0) child) := by
 simp only [run,h,if_true]

theorem snapshot_frame (a : Args) : (before a).1.sdk.state = a.world.sdk.state :=
 snapshots_frame a.world.sdk (plan a)

theorem child_error (w : World) (account : Nat) (e : PE) (suffix : List RuntimeEvent) :
 finish w account (.returned (.error e) suffix) =
   .returned {w with runtime := w.runtime ++ suffix} (.error e) := rfl

theorem stopped_prefix (w : World) (account : Nat) (pre : List RuntimeEvent) :
 finish w account (.stopped pre) = .stopped w.sdk.events (w.runtime ++ pre) := rfl

/-- SAME-cell complete success frame; metadata and every other cell are
preserved by NLF.put. This is model support, not native-parent correspondence. -/
theorem written (w : World) (account : Nat) (checkpoint : Bytes)
 (free : (w.sdk.state.cells (w.sdk.state.accounts account).data).writer=none)
 (empty : (w.sdk.state.cells (w.sdk.state.accounts account).data).readers=[])
 (same : checkpoint.length=(w.sdk.state.cells (w.sdk.state.accounts account).data).payload.bytes.length) :
 writeCheckpoint w account checkpoint =
   .returned
     { w with
       sdk := { w.sdk with
         state := NLF_SdkModel.put w.sdk.state (w.sdk.state.accounts account).data
           { w.sdk.state.cells (w.sdk.state.accounts account).data with
             payload := { (w.sdk.state.cells (w.sdk.state.accounts account).data).payload with bytes := checkpoint } }
         next := w.sdk.next+1
         events := w.sdk.events ++ copyEvents w account checkpoint }
       runtime := w.runtime ++ copyRuntime w account checkpoint } (.ok ()) := by
 unfold writeCheckpoint
 rw [NLF_CopyStep.success w.sdk.state account w.sdk.next checkpoint free empty same]

#print axioms rejection
#print axioms entered
#print axioms snapshot_frame
#print axioms child_error
#print axioms stopped_prefix
#print axioms written
end NMV_Stage1
