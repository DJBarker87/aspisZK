import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace R1Z.PV_ROWS10_Entropy
/-- Boundary responses to sys_fill_exact. The positive return count is the
payload length; invalid positive counts remain explicit. This is an owned
source model, not an extraction or an installed external dictionary entry. -/
inductive Reply where
  | bytes (payload : List UInt8)
  | interrupted (writes : List UInt8)
  | error (code : Int) (writes : List UInt8)
  | unexpected (writes : List UInt8)
  deriving DecidableEq, Repr
inductive Outcome where
  | success (buffer : List UInt8)
  | failure (code : Int) (buffer : List UInt8)
  | prefix (buffer : List UInt8)
  deriving DecidableEq, Repr
/-- Memory written by the boundary is retained on EVERY return branch. An
arbitrary full-buffer replacement is represented by a list of the same length;
a shorter list represents a prefix write. Slice metadata never changes. -/
def overwrite (todo writes : List UInt8) : List UInt8 :=
  writes.take todo.length ++ todo.drop writes.length
 theorem overwrite_length (todo writes : List UInt8) :
    (overwrite todo writes).length = todo.length := by
  simp only [overwrite, List.length_append, List.length_take, List.length_drop]
  omega
/-- Exhausted response tape means an unfinished finite prefix, never a proof
of native divergence. On error the buffer includes all earlier writes. -/
def run : List Reply → List UInt8 → List UInt8 → Outcome
  | _, [], done => .success done
  | [], todo@(_ :: _), done => .prefix (done ++ todo)
  | .interrupted writes :: rs, todo@(_ :: _), done => run rs (overwrite todo writes) done
  | .error code writes :: _, todo@(_ :: _), done => .failure code (done ++ overwrite todo writes)
  | .unexpected writes :: _, todo@(_ :: _), done => .failure 0 (done ++ overwrite todo writes)
  | .bytes payload :: rs, todo@(_ :: _), done =>
    if payload.isEmpty || todo.length < payload.length then
      .failure 0 (done ++ overwrite todo payload)
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
  | .interrupted _ => .interrupted
  | .error c _ => .error c
  | .unexpected _ => .unexpected
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
    (xs done writes : List UInt8) (code : Int) :
    run (.error code writes :: rs) (x::xs) done =
      .failure code (done ++ overwrite (x::xs) writes) := rfl
 theorem interrupted_retries (rs : List Reply) (x : UInt8)
    (xs done writes : List UInt8) :
    run (.interrupted writes :: rs) (x::xs) done =
      run rs (overwrite (x::xs) writes) done := rfl
 theorem failure_control (rs : List Reply) (todo done : List UInt8) :
    failed (run rs todo done) = signal (rs.map control) todo.length := by
  induction rs generalizing todo done with
  | nil => cases todo <;> rfl
  | cons r rs ih =>
    cases todo with
    | nil => simp [run, failed, signal]
    | cons x xs =>
      cases r with
      | interrupted writes =>
        simpa only [run, List.map_cons, control, signal, overwrite_length] using
          ih (overwrite (x::xs) writes) done
      | error c writes => rfl
      | unexpected writes => rfl
      | bytes p =>
        simp only [run, List.map_cons, control, List.length_cons, signal]
        by_cases h : p = []
        · subst p; simp [failed]
        · have hp : p.isEmpty = false := by cases p <;> simp_all
          have hn : ¬ p.length = 0 := by simpa using h
          simp only [hp, Bool.false_or, hn, decide_false, Bool.false_or]
          split <;> rename_i hc
          · rfl
          · simpa using ih ((x::xs).drop p.length) (done ++ p)
def buffer : Outcome → List UInt8
  | .success b | .failure _ b | .prefix b => b
 theorem buffer_length (rs : List Reply) (todo done : List UInt8) :
    (buffer (run rs todo done)).length = done.length + todo.length := by
  induction rs generalizing todo done with
  | nil => cases todo <;> simp [run, buffer]
  | cons r rs ih =>
    cases todo with
    | nil => simp [run, buffer]
    | cons x xs =>
      cases r with
      | interrupted writes =>
        simpa only [run, overwrite_length] using ih (overwrite (x::xs) writes) done
      | error c writes => simp [run, buffer, overwrite_length]
      | unexpected writes => simp [run, buffer, overwrite_length]
      | bytes p =>
        simp only [run]
        split <;> rename_i h
        · simp [buffer, overwrite_length]
        · rw [ih, List.length_append, List.length_drop]
          have hp : ¬ (x::xs).length < p.length := by
            intro hp
            apply h
            simp [hp]
          simp only [List.length_cons] at hp ⊢
          omega
 theorem public_control_suffices (a b : List Reply)
    (ta tb da db : List UInt8)
    (hc : a.map control = b.map control) (hl : ta.length = tb.length) :
    failed (run a ta da) = failed (run b tb db) := by
  rw [failure_control, failure_control, hc, hl]
#print axioms overwrite_length
#print axioms buffer_length
#print axioms public_control_suffices
/-- Successful-byte uniformity alone cannot establish a failure law: identical
public request lengths allow different errors at the external boundary. -/
theorem request_length_insufficient :
    failed (run [.error 1 []] [0] []) ≠
      failed (run [.bytes [7]] [0] []) := by decide
#print axioms consumed_signal
#print axioms run_empty
#print axioms error_preserves_partial
#print axioms interrupted_retries
#print axioms failure_control
#print axioms request_length_insufficient
end R1Z.PV_ROWS10_Entropy
