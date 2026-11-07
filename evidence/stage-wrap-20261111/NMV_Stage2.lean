import NMV_Model
set_option autoImplicit false
namespace NMV_Stage2
open NMV_Model NMV_Snapshot

def admitted (a : Args) : Bool :=
  decide (a.accounts.length = 7 ∧ a.data.take 4 = [65,83,81,56])

def plan (a : Args) : List (Nat × Nat × Nat) :=
 [(a.accounts[0]?.getD 0,58295,58295),
  (a.accounts[1]?.getD 0,384,384),
  (a.accounts[2]?.getD 0,192,192),
  (a.accounts[3]?.getD 0,768,768),
  (a.accounts[4]?.getD 0,128,256),
  (a.accounts[5]?.getD 0,192,320),
  (a.accounts[6]?.getD 0,1768,1768)]

/-- Source order: clear, seven released snapshots, Clock::get, child. -/
def before (a : Args) (clock : Except PE UInt64) : World × ChildArgs :=
 let r := snapshots a.world.sdk (plan a)
 (⟨r.1,a.world.runtime ++ [.clearReturnData] ++
    ((r.1.events.drop a.world.sdk.events.length).map RuntimeEvent.sdk) ++ [.clock clock]⟩,
  ⟨a.program,r.2,a.data,some clock⟩)

def finish (w : World) (child : ChildEnd Unit) : End Unit :=
 match child with
 | .returned result suffix => .returned {w with runtime:=w.runtime++suffix} result
 | .stopped pre => .stopped w.sdk.events (w.runtime++pre)

/-- Complete wrapper transcription over independent FULL child replies. This
is a parameterized fold, not a native producer or a credited row root. -/
def run (a : Args) (clock : Except PE UInt64) (child : ChildEnd Unit) :
    Option ChildArgs × End Unit :=
 if admitted a then
   let b := before a clock
   (some b.2,finish b.1 child)
 else (none,.returned a.world (.error .InvalidInstructionData))

theorem rejection (a : Args) (clock : Except PE UInt64) (child : ChildEnd Unit)
    (h : admitted a = false) :
    run a clock child = (none,.returned a.world (.error .InvalidInstructionData)) := by
  simp only [run,h,Bool.false_eq_true,if_false]

theorem entered (a : Args) (clock : Except PE UInt64) (child : ChildEnd Unit)
    (h : admitted a = true) :
    run a clock child = (some (before a clock).2,finish (before a clock).1 child) := by
  simp only [run,h,if_true]

theorem snapshot_frame (a : Args) (clock : Except PE UInt64) :
    (before a clock).1.sdk.state = a.world.sdk.state :=
  snapshots_frame a.world.sdk (plan a)

theorem argument_count (a : Args) (clock : Except PE UInt64) :
    (before a clock).2.accounts.length = 7 := by
  exact snapshots_count a.world.sdk (plan a)

theorem clear_clock_order (a : Args) (clock : Except PE UInt64) :
    (before a clock).1.runtime = a.world.runtime ++ [.clearReturnData] ++
      (((snapshots a.world.sdk (plan a)).1.events.drop a.world.sdk.events.length).map RuntimeEvent.sdk) ++
      [.clock clock] := rfl

theorem stopped_prefix (a : Args) (clock : Except PE UInt64)
    (pre : List RuntimeEvent) (h : admitted a = true) :
    (run a clock (.stopped pre)).2 =
      .stopped (before a clock).1.sdk.events ((before a clock).1.runtime++pre) := by
  rw [entered a clock (.stopped pre) h]
  rfl

/-- Replacing the child by its full SAME-argument packet transports the entire
outcome and argument observation, including stopped prefixes. No child-success
hypothesis is used. Both sides are explicit folds, never native row roots. -/
theorem compose (a : Args) (clock : Except PE UInt64)
    (nativeChild cohortChild : ChildEnd Unit) (packet : nativeChild = cohortChild) :
    run a clock nativeChild = run a clock cohortChild := by rw [packet]

#print axioms rejection
#print axioms entered
#print axioms snapshot_frame
#print axioms argument_count
#print axioms clear_clock_order
#print axioms stopped_prefix
#print axioms compose
end NMV_Stage2
