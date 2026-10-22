import Mathlib.Data.List.Basic
/-! Single-thread semantics of one live thread-local key. Thread creation,
key destruction and thread exit are outside this runtime contract. The
platform implementing these semantics is an explicit P6 boundary. -/
set_option autoImplicit false
namespace R1Z.ProverCommitTLS23
variable {Thread Value Output : Type} [DecidableEq Thread]

/-- An access executes its closure on the current value and stores the
closure's resulting value. Output includes errors if the caller chooses. -/
abbrev Access (Value Output : Type) := Value → Value × Output

def native (thread : Thread) (f : Access Value Output) (store : Thread → Value) :
    (Thread → Value) × Output :=
  let result := f (store thread)
  ((fun current => if current = thread then result.1 else store current), result.2)

theorem access_simulates (thread : Thread) (f : Access Value Output)
    (store : Thread → Value) :
    ((native thread f store).1 thread, (native thread f store).2) = f (store thread) := by
  simp only [native,ite_true]

theorem access_frame (thread other : Thread) (different : other ≠ thread)
    (f : Access Value Output) (store : Thread → Value) :
    (native thread f store).1 other = store other := by
  simp only [native,if_neg different]

def nativeRun (store : Thread → Value) :
    List (Thread × Access Value Output) → (Thread → Value) × List Output
  | [] => (store,[])
  | (thread,f)::tail =>
    let step := native thread f store
    let rest := nativeRun step.1 tail
    (rest.1,step.2::rest.2)

def singleRun (value : Value) : List (Access Value Output) → Value × List Output
  | [] => (value,[])
  | f::tail =>
    let step := f value
    let rest := singleRun step.1 tail
    (rest.1,step.2::rest.2)

def SingleThreaded (thread : Thread) (schedule : List (Thread × Access Value Output)) : Prop :=
  ∀ entry ∈ schedule, entry.1 = thread

/-- Exact state and all outputs for any finite schedule of access closures.
The single-thread premise is visible; no native TLS implementation equation
is silently added. -/
theorem schedule_simulates (thread : Thread) (schedule : List (Thread × Access Value Output))
    (oneThread : SingleThreaded thread schedule) (store : Thread → Value) :
    ((nativeRun store schedule).1 thread, (nativeRun store schedule).2) =
      singleRun (store thread) (schedule.map Prod.snd) := by
  induction schedule generalizing store with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨current,f⟩
    have same := oneThread (current,f) (List.mem_cons_self ..)
    change current = thread at same
    subst current
    have rest := ih (fun e he => oneThread e (List.mem_cons_of_mem _ he))
      (native thread f store).1
    simp only [nativeRun,singleRun,List.map_cons]
    rw [show (native thread f store).1 thread = (f (store thread)).1 by
      simp only [native,ite_true]] at rest
    exact congrArg (fun p : Value × List Output => (p.1,(f (store thread)).2::p.2)) rest

/-- Last stored value is what the next read returns, for the same live key. -/
theorem read_after_store (thread : Thread) (store : Thread → Value) (value : Value) :
    (native thread (fun v => (v,v))
      (native thread (fun _ => (value,())) store).1).2 = value := by
  simp only [native,ite_true]

#print axioms access_simulates
#print axioms access_frame
#print axioms schedule_simulates
#print axioms read_after_store
end R1Z.ProverCommitTLS23
