import NLF_Bracket
set_option autoImplicit false
namespace NLF_SnapshotEvents
open NLF_RefCell NLF_SdkModel NLF_ParentModel
/-- Acquire/deref/drop in snapshot's lexical scope. A returned error carries
no guard. Native allocation/copy of owned bytes is a caller obligation. -/
def events (s : State) (a t : Nat) : List Event :=
  match (try_borrow_data s a t).2 with
  | .error e => [.acquire a t .shared (.error e)]
  | .ok g => [.acquire a t .shared (.ok g),.deref g (.ok (s.cells g.cell).payload),.release g (.ok ())]

def step (p : Parent) (a : Nat) : Parent × Except ProgramError Payload :=
  let r := NLF_Bracket.snapshot p.state a p.next
  (⟨r.1,p.next+1,p.events ++ events p.state a p.next⟩,r.2)

theorem step_frame (p : Parent) (a : Nat) : (step p a).1.state = p.state := by
  exact NLF_Bracket.snapshot_frame p.state a p.next

theorem step_next (p : Parent) (a : Nat) : (step p a).1.next = p.next+1 := rfl

theorem step_invariant (p : Parent) (a : Nat) (h : Invariant p) :
    Invariant (step p a).1 := by
  change ValidState (NLF_Bracket.snapshot p.state a p.next).1 ∧
    Below (NLF_Bracket.snapshot p.state a p.next).1 (p.next+1) ∧
    Unique (NLF_Bracket.snapshot p.state a p.next).1
  rw [NLF_Bracket.snapshot_frame]
  exact ⟨h.1,below_succ _ _ h.2.1,h.2.2⟩

theorem step_ok_events (p : Parent) (a : Nat)
    (free : (p.state.cells (p.state.accounts a).data).writer = none)
    (fresh : p.next ∉ (p.state.cells (p.state.accounts a).data).readers)
    (bound : (p.state.cells (p.state.accounts a).data).readers.length < 9223372036854775807) :
    (step p a).1.events = p.events ++
      [.acquire a p.next .shared (.ok ⟨(p.state.accounts a).data,p.next,.shared⟩),
       .deref ⟨(p.state.accounts a).data,p.next,.shared⟩ (.ok (p.state.cells (p.state.accounts a).data).payload),
       .release ⟨(p.state.accounts a).data,p.next,.shared⟩ (.ok ())] := by
  simp [step,events,try_borrow_data,shared_result p.state _ p.next free fresh bound]

#print axioms step_frame
#print axioms step_next
#print axioms step_invariant
#print axioms step_ok_events
end NLF_SnapshotEvents
