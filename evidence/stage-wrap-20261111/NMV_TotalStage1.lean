import NMV_TotalStage2
import NMV_Stage1
set_option autoImplicit false
namespace NMV_TotalStage1
open NMV_Model NMV_Snapshot NMV_TotalSnapshot NMV_TotalFold NMV_TotalStage2

def copy (w : World) (account : Nat) (checkpoint : Bytes) : Outcome (Except PE Unit) :=
 match NMV_Stage1.writeCheckpoint w account checkpoint with
 | .returned after reply => .returned after reply
 | .stopped _ trace => .stopped .copyAbort trace

def finish (w : World) (account : Nat) : Child Bytes → Outcome (Except PE Unit)
 | .returned (.error e) events => .returned {w with runtime:=w.runtime++events} (.error e)
 | .returned (.ok checkpoint) events => copy {w with runtime:=w.runtime++events} account checkpoint
 | .stopped cause events => .stopped cause (w.runtime++events)

def run (a : Args) (allocation : List Bool) (child : ChildArgs → Child Bytes) :
    Outcome (Except PE Unit) :=
 if NMV_Stage1.admitted a then
   bind (snapshots a.world allocation (NMV_Stage1.plan a)) (fun w owned =>
     let args : ChildArgs := ⟨a.program,owned,a.data,none⟩
     finish w (a.accounts[2]?.getD 0) (child args))
 else .returned a.world (.error .InvalidInstructionData)

theorem rejection (a : Args) (allocation : List Bool) (child : ChildArgs → Child Bytes)
 (rejected : NMV_Stage1.admitted a = false) :
 run a allocation child = .returned a.world (.error .InvalidInstructionData) := by
 simp only [run,rejected,Bool.false_eq_true,if_false]

theorem snapshot_stop (a : Args) (allocation : List Bool) (child : ChildArgs → Child Bytes)
 (cause : Stop) (events : List RuntimeEvent)
 (entered : NMV_Stage1.admitted a = true)
 (stopped : snapshots a.world allocation (NMV_Stage1.plan a) = .stopped cause events) :
 run a allocation child = .stopped cause events := by
 simp only [run,entered,if_true,stopped,NMV_TotalFold.bind]

theorem child_error (w : World) (account : Nat) (error : PE) (events : List RuntimeEvent) :
 finish w account (.returned (.error error) events) =
 .returned {w with runtime:=w.runtime++events} (.error error) := rfl

theorem child_stop (w : World) (account : Nat) (cause : Stop) (events : List RuntimeEvent) :
 finish w account (.stopped cause events) = .stopped cause (w.runtime++events) := rfl

theorem replace_child (a : Args) (allocation : List Bool)
 (native reference : ChildArgs → Child Bytes) (packet : ∀ args, native args=reference args) :
 run a allocation native = run a allocation reference := by
 have equal : native = reference := funext packet
 rw [equal]

#print axioms rejection
#print axioms snapshot_stop
#print axioms child_error
#print axioms child_stop
#print axioms replace_child
end NMV_TotalStage1
