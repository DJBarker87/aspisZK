import PV_DIAG7_Effects
/-! Public adaptive diagnostic programs. The program carries public operands
and continuations. It may branch on every OS reply. This does not establish
that a witness-bearing client invocation is such a program. -/
set_option autoImplicit false
namespace PV_DIAG7
open PV_DIAG3
inductive Program where
 | done (result : Reply)
 | returned (bytes : Bytes) (next : Program)
 | call (request : Request) (next : Reply → Program)
/-- Total decoding of our typed effect result; the fallback is unreachable
by effect_has_value, and is not a replacement OS outcome. -/
def answer (signal : Signal) (q : Request) (s : State) : Reply :=
 match (effect signal q s).exit with
 | .value r => r
 | _ => .enabled false
def run (signal : Signal) : Program → Op State Reply
 | .done r => pure r
 | .returned bs next => fun s => prepend [.returned bs] (run signal next s)
 | .call q next => fun s => prepend (effect signal q s).events
     (run signal (next (answer signal q s)) (effect signal q s).state)
def calls (signal : Signal) : Program → State → List Request
 | .done _,_ => []
 | .returned _ next,s => calls signal next s
 | .call q next,s => q :: calls signal (next (answer signal q s)) (effect signal q s).state
theorem answer_correct (signal : Signal) (q : Request) (s : State) :
 (effect signal q s).exit = .value (answer signal q s) := by
 obtain ⟨r,hr⟩ := effect_has_value signal q s
 simp only [answer,hr]
#print axioms answer_correct
theorem run_done (signal : Signal) (r : Reply) (s : State) :
 run signal (.done r) s = ⟨[],s,.value r⟩ := rfl
#print axioms run_done
theorem run_returned (signal : Signal) (bs : Bytes) (next : Program) (s : State) :
 run signal (.returned bs next) s = prepend [.returned bs] (run signal next s) := rfl
#print axioms run_returned
theorem run_call_is_bind (signal : Signal) (q : Request) (next : Reply → Program) (s : State) :
 run signal (.call q next) s = bind (effect signal q s) (fun r => run signal (next r)) := by
 simp only [run,PV_DIAG3.bind,answer_correct]
#print axioms run_call_is_bind
theorem run_public (a b : Signal) (p q : Program) (s t : State)
 (he : a = b) (hp : p = q) (hs : s = t) : run a p s = run b q t := by
 cases he; cases hp; cases hs; rfl
#print axioms run_public
theorem calls_public (a b : Signal) (p q : Program) (s t : State)
 (he : a = b) (hp : p = q) (hs : s = t) : calls a p s = calls b q t := by
 cases he; cases hp; cases hs; rfl
#print axioms calls_public
theorem run_events_public (a b : Signal) (p q : Program) (s t : State)
 (he : a = b) (hp : p = q) (hs : s = t) : (run a p s).events = (run b q t).events :=
 congrArg Execution.events (run_public a b p q s t he hp hs)
#print axioms run_events_public
theorem run_terminal_public (a b : Signal) (p q : Program) (s t : State)
 (he : a = b) (hp : p = q) (hs : s = t) : (run a p s).exit = (run b q t).exit :=
 congrArg Execution.exit (run_public a b p q s t he hp hs)
#print axioms run_terminal_public
theorem run_state_public (a b : Signal) (p q : Program) (s t : State)
 (he : a = b) (hp : p = q) (hs : s = t) : (run a p s).state = (run b q t).state :=
 congrArg Execution.state (run_public a b p q s t he hp hs)
#print axioms run_state_public
theorem run_has_value (signal : Signal) (p : Program) (s : State) :
 ∃ r, (run signal p s).exit = .value r := by
 induction p generalizing s with
 | done r => exact ⟨r,rfl⟩
 | returned bs next ih => exact ih s
 | call q next ih => exact ih (answer signal q s) (effect signal q s).state
#print axioms run_has_value
theorem returned_order (signal : Signal) (a b : Bytes) (p : Program) (s : State) :
 (run signal (.returned a (.returned b p)) s).events =
 .returned a :: .returned b :: (run signal p s).events := rfl
#print axioms returned_order
theorem return_preserves_calls (signal : Signal) (bs : Bytes) (p : Program) (s : State) :
 calls signal (.returned bs p) s = calls signal p s := rfl
#print axioms return_preserves_calls
theorem call_is_first (signal : Signal) (q : Request) (next : Reply → Program) (s : State) :
 calls signal (.call q next) s = q :: calls signal (next (answer signal q s)) (effect signal q s).state := rfl
#print axioms call_is_first
theorem write_success_continuation (signal : Signal) (fd n : Nat) (bs : Bytes)
 (next : Reply → Program) (s : State) (h : signal.write fd s.cursor = .ok n) :
 run signal (.call (.write fd bs) next) s =
 prepend [.requested fd bs,.delivered fd (bs.take n)]
   (run signal (next (.write (.ok n))) (advance s)) := by
 rw [run_call_is_bind]
 change PV_DIAG3.bind (write signal fd bs s) _ = _
 rw [write_success signal fd n bs s h]
 rfl
#print axioms write_success_continuation
theorem write_error_continuation (signal : Signal) (fd : Nat) (bs : Bytes)
 (next : Reply → Program) (s : State) (e : OsError)
 (h : signal.write fd s.cursor = .error e) :
 run signal (.call (.write fd bs) next) s =
 prepend [.requested fd bs] (run signal (next (.write (.error e))) (store s e)) := by
 rw [run_call_is_bind]
 change PV_DIAG3.bind (write signal fd bs s) _ = _
 rw [write_failure signal fd bs s e h]
 rfl
#print axioms write_error_continuation
theorem interrupted_keeps_prior_delivery (signal : Signal) (fd n : Nat) (bs : Bytes)
 (next : Reply → Program) (s : State) (h : signal.write fd s.cursor = .ok n) :
 ∃ suffix, (run signal (.call (.write fd bs) next) s).events =
 [.requested fd bs,.delivered fd (bs.take n)] ++ suffix := by
 rw [write_success_continuation signal fd n bs next s h]
 exact ⟨_,rfl⟩
#print axioms interrupted_keeps_prior_delivery
theorem flush_failure_continuation (signal : Signal) (fd : Nat) (next : Reply → Program)
 (s : State) (e : OsError) (h : signal.flush fd s.cursor = some e) :
 run signal (.call (.flush fd) next) s = run signal (next (.status (some e))) (store s e) := by
 rw [run_call_is_bind,flush_failure signal fd s e h]
 exact prepend_nil _
#print axioms flush_failure_continuation
theorem file_failure_continuation (signal : Signal) (op : Nat) (path : Bytes)
 (next : Reply → Program) (s : State) (e : OsError) (h : signal.file op s.cursor = some e) :
 run signal (.call (.file op path) next) s = run signal (next (.status (some e))) (store s e) := by
 rw [run_call_is_bind,file_failure signal op path s e h]
 exact prepend_nil _
#print axioms file_failure_continuation
theorem strerror_is_precursor (signal : Signal) (code : Int) (next : Reply → Program) (s : State) :
 run signal (.call (.strerror code) next) s =
 run signal (next (.bytes (signal.strerror code))) (advance s) := by
 rw [run_call_is_bind]
 exact prepend_nil _
#print axioms strerror_is_precursor
theorem os_failure_does_not_erase_returned (signal : Signal) (bs : Bytes) (p : Program) (s : State) :
 ∃ suffix, (run signal (.returned bs p) s).events = [.returned bs] ++ suffix := ⟨_,rfl⟩
#print axioms os_failure_does_not_erase_returned
theorem all_prefix_programs_public {P C : Type} (program : P → C → Nat → Program)
 (state : P → C → State) (a b : Signal) (p q : P) (c d : C)
 (he : a = b) (hp : p = q) (hc : c = d) :
 (fun n => run a (program p c n) (state p c)) =
 (fun n => run b (program q d n) (state q d)) := by cases he; cases hp; cases hc; rfl
#print axioms all_prefix_programs_public
theorem occurrence_order_content_joint {P C : Type} (program : P → C → Program)
 (state : P → C → State) (signal : Signal) (p q : P) (c d : C)
 (hp : p = q) (hc : c = d) :
 (calls signal (program p c) (state p c),(run signal (program p c) (state p c)).events,
  (run signal (program p c) (state p c)).exit) =
 (calls signal (program q d) (state q d),(run signal (program q d) (state q d)).events,
  (run signal (program q d) (state q d)).exit) := by cases hp; cases hc; rfl
#print axioms occurrence_order_content_joint
end PV_DIAG7
