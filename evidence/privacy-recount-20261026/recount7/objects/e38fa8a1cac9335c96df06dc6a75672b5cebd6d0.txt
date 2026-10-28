import R1Z.ProverCommitTreeMap22
/-! Operation-level specification for source map gates. The induction below
is conditional on universal insert/get contracts; bounded Rust gates alone
do not supply those contracts for arbitrary tree height. -/
set_option autoImplicit false
namespace R1Z.ProverCommitTreeOps23
variable {Key Value State : Type} {cmp : Key → Key → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

def treeInsert (tree : Std.TreeMap Key Value cmp) (key : Key) (value : Value) :
    Std.TreeMap Key Value cmp × Option Value := (tree.insert key value,tree[key]?)

def runWrites (insert : State → Key → Value → State × Option Value)
    (state : State) : List (Key × Value) → State × List (Option Value)
  | [] => (state,[])
  | (key,value)::tail =>
    let step := insert state key value
    let rest := runWrites insert step.1 tail
    (rest.1,step.2::rest.2)

/-- Arbitrary write schedules, including repeats: the final map and the
entire sequence of previous answers follow from the two insert obligations.
These obligations are explicit named hypotheses, not a Rust source instance. -/
theorem writes_decode (decode : State → Std.TreeMap Key Value cmp)
    (insert : State → Key → Value → State × Option Value)
    (insert_state : ∀ s key value, decode (insert s key value).1 = (decode s).insert key value)
    (insert_previous : ∀ s key value, (insert s key value).2 = (decode s)[key]?)
    (schedule : List (Key × Value)) (state : State) :
    (decode (runWrites insert state schedule).1,(runWrites insert state schedule).2) =
      runWrites treeInsert (decode state) schedule := by
  induction schedule generalizing state with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨key,value⟩
    have rest := ih (insert state key value).1
    rw [insert_state] at rest
    simp only [runWrites,treeInsert]
    rw [insert_previous]
    exact congrArg (fun p => (p.1,(decode state)[key]?::p.2)) rest

/-- Exact get specification, composed with the existing universal list model. -/
theorem get_decode [DecidableEq Key] [DecidableEq Value]
    (decode : State → Std.TreeMap Key Value cmp) (get : State → Key → Option Value)
    (get_spec : ∀ s key, get s key = (decode s)[key]?) (state : State) (key : Key) :
    get state key = ProverCommitTable20.lookup (decode state).toList key := by
  rw [get_spec,ProverCommitTreeMap22.lookup_toList]

/-- Iterator specification preserves the unconsumed suffix, rather than only
membership of returned entries. The Rust cursor representation is separate. -/
def iterSteps {Entry : Type} : Nat → List Entry → List Entry × List Entry
  | 0, entries => ([],entries)
  | _+1, [] => ([],[])
  | n+1, entry::tail =>
    let rest := iterSteps n tail
    (entry::rest.1,rest.2)

theorem iterSteps_spec {Entry : Type} (n : Nat) (entries : List Entry) :
    iterSteps n entries = (entries.take n,entries.drop n) := by
  induction n generalizing entries with
  | zero => rfl
  | succ n ih =>
    cases entries with
    | nil => rfl
    | cons entry tail => simp only [iterSteps,ih,List.take_succ_cons,List.drop_succ_cons]

theorem tree_iteration (tree : Std.TreeMap Key Value cmp) (n : Nat) :
    (iterSteps n tree.toList).1 ++ (iterSteps n tree.toList).2 = tree.toList := by
  rw [iterSteps_spec]
  exact List.take_append_drop n tree.toList

#print axioms writes_decode
#print axioms get_decode
#print axioms iterSteps_spec
#print axioms tree_iteration
end R1Z.ProverCommitTreeOps23
