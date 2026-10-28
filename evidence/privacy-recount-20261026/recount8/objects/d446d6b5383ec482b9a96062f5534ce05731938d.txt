import R1Z.ProverCommitSimulatorInsert19
/-! Per-entry programming semantics. The source BTreeMap return-value boundary
and owned Vec/List transport remain distinct from this finite induction. -/
set_option autoImplicit false
namespace R1Z.ProverCommitTable20
variable {Key Value : Type} [DecidableEq Key] [DecidableEq Value]
abbrev Table (Key Value : Type) := List (Key × Value)

def lookup (table : Table Key Value) (key : Key) : Option Value :=
  match table with
  | [] => none
  | (k,v)::tail => if k=key then some v else lookup tail key

def conflict (old : Option Value) (answer : Value) : Bool :=
  match old with
  | none => false
  | some previous => decide (previous≠answer)

def insert (table : Table Key Value) (key : Key) (answer : Value) (collision : Bool) :
    Table Key Value × Bool :=
  match table with
  | [] => ([(key,answer)],collision)
  | (k,v)::tail =>
    if k=key then ((k,answer)::tail,collision || decide (v≠answer))
    else let out := insert tail key answer collision
         ((k,v)::out.1,out.2)

/-- The collision branch is needed only for the first matching table entry.
No key uniqueness assumption is necessary for first-match lookup. -/
theorem insert_collision (table : Table Key Value) (key : Key) (answer : Value)
    (collision : Bool) :
    (insert table key answer collision).2 = (collision || conflict (lookup table key) answer) := by
  induction table with
  | nil => simp only [insert,lookup,conflict,Bool.or_false]
  | cons entry tail ih =>
    rcases entry with ⟨k,v⟩
    by_cases same : k=key
    · simp only [insert,lookup,same,if_true,conflict]
    · simp only [insert,lookup,same,if_false,ih]

/-- Every individual address gets the overwritten answer or its prior lookup.
This is a finite entry induction, not an enumeration of keys or byte tables. -/
theorem insert_lookup (table : Table Key Value) (key query : Key) (answer : Value)
    (collision : Bool) :
    lookup (insert table key answer collision).1 query =
      if key=query then some answer else lookup table query := by
  induction table with
  | nil => simp only [insert,lookup]
  | cons entry tail ih =>
    rcases entry with ⟨k,v⟩
    by_cases same : k=key
    · subst k
      simp only [insert,if_true,lookup]
      split_ifs <;> rfl
    · simp only [insert,same,if_false,lookup,ih]
      by_cases hit : k=query
      · have miss : key≠query := by intro h;exact same (hit.trans h.symm)
        simp only [hit,if_true,miss,if_false]
      · simp only [hit,if_false]

def writes (table : Table Key Value) (collision : Bool) : List (Key × Value) →
    Table Key Value × Bool
  | [] => (table,collision)
  | (key,answer)::tail =>
    let next := insert table key answer collision
    writes next.1 next.2 tail

def oracleWrites (oracle : Key → Option Value) : List (Key × Value) → Key → Option Value
  | [] => oracle
  | (key,answer)::tail => oracleWrites (fun query => if key=query then some answer else oracle query) tail

/-- Complete finite write sequence: repeated addresses retain last-write
semantics. Applying any common fallback preserves every unprogrammed answer. -/
theorem writes_lookup (entries table : Table Key Value) (collision : Bool) (query : Key) :
    lookup (writes table collision entries).1 query = oracleWrites (lookup table) entries query := by
  induction entries generalizing table collision with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨key,answer⟩
    simp only [writes,oracleWrites]
    rw [ih]
    have lookupEq : lookup (insert table key answer collision).1 =
        (fun query => if key=query then some answer else lookup table query) := by
      funext q
      exact insert_lookup table key q answer collision
    rw [lookupEq]

theorem collision_sticky (table : Table Key Value) (entries : Table Key Value) :
    (writes table true entries).2=true := by
  induction entries generalizing table with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨key,answer⟩
    simp only [writes,insert_collision,Bool.true_or]
    exact ih _

#print axioms insert_collision
#print axioms insert_lookup
#print axioms writes_lookup
#print axioms collision_sticky
end R1Z.ProverCommitTable20
