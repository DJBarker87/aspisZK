import R1Z.ProverRwRngOwnerCertificate
import R1Z.SideChannelL1AttemptRecord
set_option autoImplicit false
noncomputable section
namespace PV_L1_EntropyProducer
open Aeneas Aeneas.Std Result
open R1Z ProverRwRng ProverRwRngControl ProverRwRngOwnerEvents ProverRwRngOwnerInventory
variable [ErasureFns]

/-- OS tags are retained; raw seed bytes are not an observation. Tape
unavailability is separately excluded by the source execution certificate. -/
def statusOf : Option ProverRwRngTape.Reply → SideChannelL1AttemptRecord.IOStatus
  | none => .error "unavailable extraction tape"
  | some (_, .Ok _) => .ok
  | some (_, .Err e) => .error ("getrandom:" ++ toString e.val)

def drawEvents (p : Tape) (n : Nat) : List SideChannelL1AttemptRecord.Event :=
  (List.range' p.used.val n).flatMap fun i =>
    [.call .rng i,.rngReturn (statusOf p.replies.val[i]?)]

def replayEvents (states : List ProverRwRngOwnerEvents.State) :
    List SideChannelL1AttemptRecord.Event :=
  (ProverRwRngOwnerInventory.events states).flatMap fun event =>
    [.call .rng event.2.1,.rngReturn (statusOf event.2.2)]

/-- This emitter calls the actual supplied-tape source owner. It does not
accept an arbitrary event callback or assume equality to a desired log. -/
def produce (nonce : Array U8 32#usize) (p : Tape) :
    Result ((List SideChannelL1AttemptRecord.Event × Status) × Tape) := do
  let (after,status) ← owner nonce p
  ok ((drawEvents p (after.used.val-p.used.val),status),after)

theorem source_replay (nonce : Array U8 32#usize) (p after : Tape) (status : Status)
    (executed : owner nonce p = ok (after,status)) :
    ∃ states,
      OwnerReplay (newBody nonce) id nonce p states (after,status) ∧
      produce nonce p = ok ((replayEvents states,status),after) ∧
      after.used.val = p.used.val + drawCount states ∧ drawCount states ≤ 16 ∧
      ∀ event ∈ ProverRwRngOwnerInventory.events states, event.2.2.isSome = true := by
  obtain ⟨states,oldPath,path,replies,cursor,bound,history,available,suffix⟩ :=
    (ProverRwRngOwnerCertificate.universal_cap16 nonce p).2 after status executed
  refine ⟨states,path,?_,cursor,bound,available⟩
  have count : after.used.val-p.used.val = drawCount states := by omega
  simp only [produce,executed,bind_tc_ok]
  rw [count]
  simp only [drawEvents,replayEvents,history,List.flatMap_map]
  rfl
#print axioms source_replay
end PV_L1_EntropyProducer
