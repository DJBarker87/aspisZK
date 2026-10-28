import R1Z.GamesR1PBin
/-! Source entropy adapter, before reservation and the eight-attempt loop.
This preserves the 16-draw rejection limit, OS failure and retained state.
It is not the full shipped FS experiment and assumes no OS probability law.
`Candidate` groups the source's consecutive 32-byte slices of its 96-byte draw.
The source/Lean translation remains a P6 component boundary. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEntropy18
open R0Z.FsStatement R1Z.GamesR1PBin
attribute [local instance] Classical.propDecidable

abbrev Candidate := Fin 3 → OracleAnswer

def decode (raw : Candidate) : Option SecP :=
  if good : ∀ i, raw i ≠ 0 then some (fun i => ⟨raw i, good i⟩) else none

inductive Error (OsError : Type) where
  | os : OsError → Error OsError
  | repeatedZero : Error OsError
  deriving DecidableEq

/-- The draw state can retain the complete OS-call history. Only the next
96-byte draw is consumed; no input is inspected after success or OS error. -/
def run {State OsError : Type}
    (next : State → Except OsError Candidate × State) :
    Nat → State → Except (Error OsError) SecP × State
  | 0, state => (.error .repeatedZero, state)
  | fuel+1, state =>
    let (status, after) := next state
    match status with
    | .error e => (.error (.os e), after)
    | .ok raw =>
      match decode raw with
      | some secrets => (.ok secrets, after)
      | none => run next fuel after

def generate {State OsError : Type} (next : State → Except OsError Candidate × State)
    (state : State) : Except (Error OsError) SecP × State := run next 16 state

theorem decode_success (secrets : SecP) :
    decode (fun i => (secrets i).val) = some secrets := by
  simp only [decode, dif_pos (fun i => (secrets i).property)]

theorem decode_zero : decode (fun _ => 0) = none := by
  simp only [decode]
  split
  · next good => exact False.elim (good 0 rfl)
  · rfl

theorem os_error {State OsError : Type} (next : State → Except OsError Candidate × State)
    (state after : State) (error : OsError) (fuel : Nat)
    (failed : next state = (.error error, after)) :
    run next (fuel+1) state = (.error (.os error), after) := by
  simp only [run, failed]

theorem success {State OsError : Type} (next : State → Except OsError Candidate × State)
    (state after : State) (secrets : SecP) (fuel : Nat)
    (drawn : next state = (.ok (fun i => (secrets i).val), after)) :
    run next (fuel+1) state = (.ok secrets, after) := by
  simp only [run, drawn, decode_success]

/-- All-zero draws are a possible source input and consume the entire limit.
There is no deterministic replacement by nonzero secrets preserving status. -/
theorem zero_draws {State OsError : Type} (advance : State → State)
    (fuel : Nat) (state : State) :
    run (fun s => ((.ok (fun _ => 0) : Except OsError Candidate), advance s)) fuel state =
      (.error .repeatedZero, advance^[fuel] state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [run, decode_zero]
    rw [ih, Function.iterate_succ_apply]

/-- A type-level adapter from successful generation is exact, but cannot be
extended to every source trace while preserving the actual error status. -/
theorem no_total_success_adapter {OsError : Type} :
    ¬ ∃ adapt : Except (Error OsError) SecP → SecP,
      ∀ result : Except (Error OsError) SecP, result = Except.ok (adapt result) := by
  rintro ⟨adapt, preserves⟩
  have impossible := preserves (Except.error Error.repeatedZero)
  cases impossible

/-- Changing any unused suffix of the draw stream has no effect on a
successful first draw, including the retained state at that boundary. -/
theorem success_ignores_suffix {State OsError : Type}
    (left right : State → Except OsError Candidate × State)
    (state after : State) (secrets : SecP) (fuel : Nat)
    (hl : left state = (.ok (fun i => (secrets i).val), after))
    (hr : right state = (.ok (fun i => (secrets i).val), after)) :
    run left (fuel+1) state = run right (fuel+1) state := by
  rw [success left state after secrets fuel hl, success right state after secrets fuel hr]

#print axioms decode_success
#print axioms decode_zero
#print axioms os_error
#print axioms success
#print axioms zero_draws
#print axioms no_total_success_adapter
#print axioms success_ignores_suffix
end R1Z.ProverCommitEntropy18
