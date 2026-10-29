import NEF_ObserverEffects
set_option autoImplicit false
namespace NEF
/-- The query's pre-mark beforeMark can reject with any error and any beforeMark effects. -/
def queryWithMark {A Err S E P : Type}
    (beforeMark : S → Outcome (Except Err A) S E) (phase : P) (s : S) :
    Outcome (Except Err A) S E :=
  let out := beforeMark s
  match out.result with
  | .error _ => out
  | .ok _ =>
    let (_, state, events) := @mark P S E none phase out.state
    { out with state := state, effects := out.effects ++ events }

theorem query_values_mark_erasure {A Err S E P : Type}
    (beforeMark : S → Outcome (Except Err A) S E) (phase : P) (s : S) :
    queryWithMark beforeMark phase s = beforeMark s := by
  simp only [queryWithMark, mark]
  split
  · rfl
  · simp only [List.append_nil]

/-- Unroll only a symbolic number of small steps, preserving all rejection states. -/
def iterate {S : Type} (step : S → S) : Nat → S → S
  | 0, s => s
  | n+1, s => iterate step n (step s)

theorem loop_step_transport {S : Type} (native erased : S → S)
    (stepLaw : ∀ s, native s = erased s) (n : Nat) (s : S) :
    iterate native n s = iterate erased n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [iterate, stepLaw, ih]

theorem query_loop_mark_erasure {A Err S E P : Type}
    (beforeMark : Outcome (Except Err A) S E → Outcome (Except Err A) S E)
    (phase : P) (n : Nat) (initial : Outcome (Except Err A) S E) :
    iterate (fun s => queryWithMark (fun _ : S => beforeMark s) phase (beforeMark s).state) n initial = iterate beforeMark n initial := by
  exact loop_step_transport _ _ (fun s => query_values_mark_erasure (fun _ : S => beforeMark s) phase (beforeMark s).state) n initial
#print axioms query_values_mark_erasure
#print axioms loop_step_transport
#print axioms query_loop_mark_erasure
end NEF
