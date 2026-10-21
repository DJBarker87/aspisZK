import R1Z.ProverCommitTrustedStd24
/-! Adaptive ordered-map callers over the D133 interface. Continuations can
branch on insertion's previous answer, lookup, or the complete ordered
iterator. Terminal values can retain errors; no success-only projection is
used. This does not identify an extracted caller with this program. -/
set_option autoImplicit false
namespace R1Z.ProverCommitMapProgram24
open ProverCommitTrustedStd24
variable {Key Value State Thread Slot Output Terminal : Type}
variable {cmp : Key → Key → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

inductive Program (Key Value Terminal : Type) where
  | done (out : Terminal)
  | insert (key : Key) (value : Value) (next : Option Value → Program Key Value Terminal)
  | get (key : Key) (next : Option Value → Program Key Value Terminal)
  | iter (next : List (Key × Value) → Program Key Value Terminal)

inductive Reply (Key Value : Type) where
  | inserted (key : Key) (value : Value) (previous : Option Value)
  | got (key : Key) (answer : Option Value)
  | enumerated (entries : List (Key × Value))

def run (map : MapAPI Key Value State cmp) :
    Program Key Value Terminal → State → State × List (Reply Key Value) × Terminal
  | .done out, state => (state,[],out)
  | .insert key value next, state =>
    let step := map.insert state key value
    let rest := run map (next step.2) step.1
    (rest.1,Reply.inserted key value step.2::rest.2.1,rest.2.2)
  | .get key next, state =>
    let answer := map.get state key
    let rest := run map (next answer) state
    (rest.1,Reply.got key answer::rest.2.1,rest.2.2)
  | .iter next, state =>
    let entries := map.entries state
    let rest := run map (next entries) state
    (rest.1,Reply.enumerated entries::rest.2.1,rest.2.2)

variable [DecidableEq Thread]
variable (map : MapAPI Key Value State cmp) (tls : TLSAPI Thread Slot Output)
  (thread : Thread) (schedule : List (Thread × ProverCommitTLS23.Access Slot Output))
  (trusted : TrustedStd map tls thread schedule)
include trusted

/-- Complete adaptive caller transport: final map representation, exact
ordered responses and terminal output, for arbitrary finite branching. -/
theorem run_decode (program : Program Key Value Terminal) (state : State) :
    (map.decode (run map program state).1,(run map program state).2) =
      run modelMap program (map.decode state) := by
  induction program generalizing state with
  | done out => rfl
  | insert key value next ih =>
    have rest := ih (map.insert state key value).2 (map.insert state key value).1
    rw [trusted.btree_insert_state,trusted.btree_insert_previous] at rest
    simp only [run,modelMap,ProverCommitTreeOps23.treeInsert]
    rw [trusted.btree_insert_previous]
    exact congrArg (fun p => (p.1,Reply.inserted key value (map.decode state)[key]?::p.2.1,p.2.2)) rest
  | get key next ih =>
    have rest := ih (map.get state key) state
    rw [trusted.btree_get] at rest
    simp only [run,modelMap]
    rw [trusted.btree_get]
    exact congrArg (fun p => (p.1,Reply.got key (map.decode state)[key]?::p.2.1,p.2.2)) rest
  | iter next ih =>
    have rest := ih (map.entries state) state
    rw [trusted.btree_iter_ordered] at rest
    simp only [run,modelMap]
    rw [trusted.btree_iter_ordered]
    exact congrArg (fun p => (p.1,Reply.enumerated (map.decode state).toList::p.2.1,p.2.2)) rest

/-- Starting at the actual trusted empty-map boundary needs no extra initial
representation premise. The same universal list is the only std premise. -/
theorem empty_run (program : Program Key Value Terminal) :
    (map.decode (run map program map.empty).1,(run map program map.empty).2) =
      run modelMap program ∅ := by
  rw [run_decode map tls thread schedule trusted,trusted.btree_empty]

#print axioms run_decode
#print axioms empty_run
end R1Z.ProverCommitMapProgram24
