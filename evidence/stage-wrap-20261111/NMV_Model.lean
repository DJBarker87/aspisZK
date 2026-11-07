import NMV_Snapshot
import NLF_CopyStep
import NLM_PacketTypes
set_option autoImplicit false
namespace NMV_Model
open NLF_SdkModel NLF_ParentModel NMV_Snapshot
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Bytes := List UInt8
/-- Whole runtime events, not success flags or hashes of buffers. -/
inductive RuntimeEvent where
  | sdk (event : NLF_ParentModel.Event)
  | checkpointWrite (account : Nat) (bytes : Bytes)
  | clearReturnData
  | clock (reply : Except PE UInt64)
  | child (site : Nat) (payload : Bytes)
  | returnData (payload : Bytes)
  | digest (input : List Bytes) (reply : Bytes)
  | errorLog (payload : Bytes)
structure World where
  sdk : Parent
  runtime : List RuntimeEvent
/-- Stopped outcomes carry only the ordered prefix, and no post-abort world. -/
inductive End (α : Type) where
  | returned (world : World) (reply : Except PE α)
  | stopped (sdkPrefix : List NLF_ParentModel.Event) (runtimePrefix : List RuntimeEvent)

structure Args where
  program : Bytes
  accounts : List Nat
  data : Bytes
  world : World
structure ChildArgs where
  program : Bytes
  accounts : List Owned
  data : Bytes
  slot : Option (Except PE UInt64)

/-- Complete child Result plus its ordered runtime suffix. Owned children have
no AccountInfo argument: they cannot mutate the original SDK cells. -/
inductive ChildEnd (α : Type) where
  | returned (reply : Except PE α) (runtime : List RuntimeEvent)
  | stopped (runtimePrefix : List RuntimeEvent)

/-- Source snapshot schedule carries the NLF token state across every call. -/
def snapshots : Parent → List (Nat × Nat × Nat) → Parent × List Owned
 | p, [] => (p,[])
 | p, (a,l₁,l₂)::rest =>
   let r := NMV_Snapshot.run p a l₁ l₂
   let tail := snapshots r.1 rest
   (tail.1,r.2::tail.2)

theorem snapshots_frame (p : Parent) (plan : List (Nat × Nat × Nat)) :
    (snapshots p plan).1.state = p.state := by
  induction plan generalizing p with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨a,l₁,l₂⟩
    change (snapshots (NMV_Snapshot.run p a l₁ l₂).1 tail).1.state = p.state
    rw [ih,NMV_Snapshot.frame]

theorem snapshots_count (p : Parent) (plan : List (Nat × Nat × Nat)) :
    (snapshots p plan).2.length = plan.length := by
  induction plan generalizing p with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨a,l₁,l₂⟩
    change ((NMV_Snapshot.run p a l₁ l₂).2 ::
      (snapshots (NMV_Snapshot.run p a l₁ l₂).1 tail).2).length = _
    simp only [List.length_cons,ih]

#print axioms snapshots_frame
#print axioms snapshots_count
end NMV_Model
