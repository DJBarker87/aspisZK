import PCM_Algebra
set_option autoImplicit false
namespace PCM
open RSL Computation
/-- Infallible RefCell::borrow maps conflict to a stopped prefix, rather than
returning AccountBorrowFailed. The successful guard remains token-indexed. -/
def panicOnError {A : Type} (m : Computation A) : Computation A := fun s env o =>
  (∃ a s1 es, m s env ⟨.ret (.ok a,s1),es⟩ ∧ o = ⟨.ret (.ok a,s1),es⟩) ∨
  (∃ e s1 es, m s env ⟨.ret (.error e,s1),es⟩ ∧ o = ⟨.abort,es⟩) ∨
  (∃ es, m s env ⟨.abort,es⟩ ∧ o = ⟨.abort,es⟩) ∨
  (∃ es, m s env ⟨.diverge,es⟩ ∧ o = ⟨.diverge,es⟩)

def dataLen (a : AccountInfo) : Computation Nat :=
  panicOnError (guardScope a .shared fun _ => do
    let s ← get
    Computation.pure (s.sdk.cells a.cell).payload.length)

def dataIsEmpty (a : AccountInfo) : Computation Bool := do
  let n ← dataLen a
  Computation.pure (n == 0)

/-- AccountInfo::lamports uses its own RefCell and infallible shared borrow.
The lamports cell mapping is a runtime-entry representation obligation. -/
def readLamports (a : AccountInfo) : Computation UInt64 := fun s env o =>
  let la : AccountInfo := { a with cell := s.lamportCell a.cell }
  ∃ ro, RSL.acquire la .shared s.lamportSdk env ro ∧
    match ro.exit with
    | .abort => o = ⟨.abort,ro.events.map Event.lamport⟩
    | .diverge => o = ⟨.diverge,ro.events.map Event.lamport⟩
    | .ret (.error _,_) => o = ⟨.abort,ro.events.map Event.lamport⟩
    | .ret (.ok t,sdk1) => ∃ rr, RSL.release la t .shared sdk1 env rr ∧
      o = ⟨(match rr.exit with
        | .ret sdk2 => .ret (.ok (s.lamports (s.lamportCell a.cell)),{s with lamportSdk := sdk2})
        | .abort => .abort | .diverge => .diverge),
        (ro.events ++ rr.events).map Event.lamport⟩
end PCM
