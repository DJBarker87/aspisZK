import NMV_TotalFold
import NMV_Stage2
set_option autoImplicit false
namespace NMV_TotalStage2
open NMV_Model NMV_Snapshot NMV_TotalSnapshot NMV_TotalFold

/-- Complete typed child termination: Rust error is a RETURN; Aeneas failure
and divergence are separate stops with exactly their chronological prefix. -/
inductive Child (α : Type) where
 | returned (reply : Except PE α) (events : List RuntimeEvent)
 | stopped (cause : Stop) (events : List RuntimeEvent)

def finish (w : World) : Child Unit → Outcome (Except PE Unit)
 | .returned reply events => .returned {w with runtime:=w.runtime++events} reply
 | .stopped cause events => .stopped cause (w.runtime++events)

/-- The observation carries the full OWNED array and exact clock reply into
one actual child occurrence; it is not a success or endpoint hypothesis. -/
structure Observation where
 args : ChildArgs
 before : World
 reply : Child Unit

def run (a : Args) (allocation : List Bool) (clock : Except PE UInt64)
 (child : ChildArgs → Child Unit) : Outcome (Except PE Unit) :=
 if NMV_Stage2.admitted a then
   let cleared := {a.world with runtime:=a.world.runtime++[.clearReturnData]}
   bind (snapshots cleared allocation (NMV_Stage2.plan a)) (fun w owned =>
     let before := {w with runtime:=w.runtime++[.clock clock]}
     let args : ChildArgs := ⟨a.program,owned,a.data,some clock⟩
     finish before (child args))
 else .returned a.world (.error .InvalidInstructionData)

theorem rejection (a : Args) (allocation : List Bool) (clock : Except PE UInt64)
 (child : ChildArgs → Child Unit) (rejected : NMV_Stage2.admitted a = false) :
 run a allocation clock child = .returned a.world (.error .InvalidInstructionData) := by
 simp only [run,rejected,Bool.false_eq_true,if_false]

/-- A snapshot stop prevents Clock::get and the owned child from entering.
There is no post-abort world or synthetic cleanup suffix. -/
theorem snapshot_stop (a : Args) (allocation : List Bool) (clock : Except PE UInt64)
 (child : ChildArgs → Child Unit) (cause : Stop) (events : List RuntimeEvent)
 (entered : NMV_Stage2.admitted a = true)
 (stopped : snapshots {a.world with runtime:=a.world.runtime++[.clearReturnData]}
   allocation (NMV_Stage2.plan a) = .stopped cause events) :
 run a allocation clock child = .stopped cause events := by
 simp only [run,entered,if_true,stopped,NMV_TotalFold.bind]

/-- Full child replacement is at the exact original program, snapshots,
instruction and slot. This is an INTERMEDIATE fold, not a positive row root. -/
theorem replace_child (a : Args) (allocation : List Bool) (clock : Except PE UInt64)
 (native reference : ChildArgs → Child Unit)
 (packet : ∀ args, native args = reference args) :
 run a allocation clock native = run a allocation clock reference := by
 have equal : native = reference := funext packet
 rw [equal]

#print axioms rejection
#print axioms snapshot_stop
#print axioms replace_child
end NMV_TotalStage2
