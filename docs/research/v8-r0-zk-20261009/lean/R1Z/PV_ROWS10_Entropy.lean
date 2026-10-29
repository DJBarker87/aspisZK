import Std.Tactic.Omega
set_option autoImplicit false
namespace R1Z.PV_ROWS10_Entropy
/-- Boundary responses to sys_fill_exact. The positive return count is the
payload length; invalid positive counts remain explicit. This is an owned
source model, not an extraction or an installed external dictionary entry. -/
inductive Reply where
  | bytes (payload : List UInt8)
  | interrupted
  | error (code : Int)
  | unexpected
  deriving DecidableEq, Repr
inductive Outcome where
  | success (buffer : List UInt8)
  | failure (code : Int) (buffer : List UInt8)
  | prefix (buffer : List UInt8)
  deriving DecidableEq, Repr
/-- Exhausted response tape means an unfinished finite prefix, never a proof
of native divergence. On error the buffer includes all earlier writes. -/
def run : List Reply → List UInt8 → List UInt8 → Outcome
  | _, [], done => .success done
  | [], todo@(_ :: _), done => .prefix (done ++ todo)
  | .interrupted :: rs, todo@(_ :: _), done => run rs todo done
  | .error code :: _, todo@(_ :: _), done => .failure code (done ++ todo)
  | .unexpected :: _, todo@(_ :: _), done => .failure 0 (done ++ todo)
  | .bytes payload :: rs, todo@(_ :: _), done =>
    if payload.isEmpty || todo.length < payload.length then
      .failure 0 (done ++ todo)
    else run rs (todo.drop payload.length) (done ++ payload)
def failed : Outcome → Bool
  | .failure _ _ => true
  | _ => false
/-- Public control projection keeps counts and errors but removes entropy bytes. -/
inductive Control where
  | bytes (count : Nat)
  | interrupted
  | error (code : Int)
  | unexpected
  deriving DecidableEq
 def control : Reply → Control
  | .bytes p => .bytes p.length
  | .interrupted => .interrupted
  | .error c => .error c
  | .unexpected => .unexpected
 def signal : List Control → Nat → Bool
  | _, 0 => false
  | [], _+1 => false
  | .interrupted :: rs, n+1 => signal rs (n+1)
  | .error _ :: _, _+1 => true
  | .unexpected :: _, _+1 => true
  | .bytes count :: rs, n+1 =>
    if count = 0 || n+1 < count then true else signal rs (n+1-count)
/-- The consumed option-B signal follows from the actual boundary's public
control word and the source binding, not from uniform successful bytes. -/
theorem consumed_signal {W : Type} (length : W → Nat)
    (trace : W → List Control) (nativeSignal : W → Bool)
    (sourceBinding : ∀ w, nativeSignal w = signal (trace w) (length w))
    (publicControl : ∀ a b, trace a = trace b)
    (publicLength : ∀ a b, length a = length b) :
    ∀ a b, nativeSignal a = nativeSignal b := by
  intro a b
  rw [sourceBinding, sourceBinding, publicControl a b, publicLength a b]
 theorem run_empty (rs : List Reply) (done : List UInt8) :
    run rs [] done = .success done := by cases rs <;> rfl
 theorem error_preserves_partial (rs : List Reply) (x : UInt8)
    (xs done : List UInt8) (code : Int) :
    run (.error code :: rs) (x::xs) done = .failure code (done ++ x::xs) := rfl
 theorem interrupted_retries (rs : List Reply) (x : UInt8)
    (xs done : List UInt8) :
    run (.interrupted :: rs) (x::xs) done = run rs (x::xs) done := rfl
 theorem failure_control (rs : List Reply) (todo done : List UInt8) :
    failed (run rs todo done) = signal (rs.map control) todo.length := by
  induction rs generalizing todo done with
  | nil => cases todo <;> rfl
  | cons r rs ih =>
    cases todo with
    | nil => simp [run, failed, signal]
    | cons x xs =>
      cases r with
      | interrupted => exact ih (x::xs) done
      | error c => rfl
      | unexpected => rfl
      | bytes p =>
        simp only [run, List.map_cons, control, List.length_cons, signal]
        by_cases h : p = []
        · subst p; simp [failed]
        · have hp : p.isEmpty = false := List.isEmpty_eq_false.mpr h
          have hn : ¬ p.length = 0 := by simpa using h
          simp only [hp, Bool.false_or, hn, decide_false, Bool.false_or]
          split <;> rename_i hc
          · rfl
          · simpa using ih ((x::xs).drop p.length) (done ++ p)
/-- Successful-byte uniformity alone cannot establish a failure law: identical
public request lengths allow different errors at the external boundary. -/
theorem request_length_insufficient :
    failed (run [.error 1] [0] []) ≠
      failed (run [.bytes [7]] [0] []) := by decide
#print axioms consumed_signal
#print axioms run_empty
#print axioms error_preserves_partial
#print axioms interrupted_retries
#print axioms failure_control
#print axioms request_length_insufficient
end R1Z.PV_ROWS10_Entropy
