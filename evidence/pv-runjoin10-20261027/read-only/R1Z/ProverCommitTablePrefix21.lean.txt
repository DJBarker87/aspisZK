import R1Z.ProverCommitTable20
/-! Arbitrary finite prefixes for the single-entry programming gate.
No finite key space or fixed table length is assumed. This module does not
identify std::BTreeMap with the owned entry representation. -/
set_option autoImplicit false
namespace R1Z.ProverCommitTablePrefix21
open ProverCommitTable20
variable {Key Value : Type} [DecidableEq Key] [DecidableEq Value]

theorem lookup_append (pre suffix : Table Key Value) (key : Key) :
    lookup (pre++suffix) key = (lookup pre key).orElse (fun _ => lookup suffix key) := by
  induction pre with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨k,v⟩
    simp only [List.cons_append,lookup]
    by_cases h : k=key
    · simp only [h,if_true,Option.orElse_some]
    · simp only [h,if_false,ih]

/-- A pre without a matching key is retained verbatim, with no collision
update. This is the induction boundary consumed by a single ProverCommitTable20.insert step. -/
theorem insert_append_miss (pre suffix : Table Key Value) (key : Key) (answer : Value)
    (collision : Bool) (miss : lookup pre key=none) :
    ProverCommitTable20.insert (pre++suffix) key answer collision =
      let out := ProverCommitTable20.insert suffix key answer collision
      (pre++out.1,out.2) := by
  induction pre with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨k,v⟩
    by_cases h : k=key
    · simp only [lookup,h,if_true] at miss
      cases miss
    · simp only [lookup,h,if_false] at miss
      simp only [List.cons_append,ProverCommitTable20.insert,h,if_false,ih miss]

/-- Exact overwrite at one entry after any missed pre. The entire suffix
and the original key are retained, and the collision flag is sticky. -/
theorem overwrite_after_prefix (pre suffix : Table Key Value) (key : Key)
    (previous answer : Value) (collision : Bool) (miss : lookup pre key=none) :
    ProverCommitTable20.insert (pre++(key,previous)::suffix) key answer collision =
      (pre++(key,answer)::suffix,collision || decide (previous≠answer)) := by
  rw [insert_append_miss pre ((key,previous)::suffix) key answer collision miss]
  simp only [ProverCommitTable20.insert,if_true]

/-- The symbolic pre in the single-entry gate is exactly first-hit lookup;
its summary also accounts for hits before the selected entry. -/
theorem entry_collision (pre suffix : Table Key Value) (key address : Key)
    (previous answer : Value) (collision : Bool) :
    (ProverCommitTable20.insert (pre++(key,previous)::suffix) address answer collision).2 =
      (collision || conflict ((lookup pre address).orElse
        (fun _ => if key=address then some previous else lookup suffix address)) answer) := by
  rw [insert_collision,lookup_append]
  rfl

#print axioms lookup_append
#print axioms insert_append_miss
#print axioms overwrite_after_prefix
#print axioms entry_collision
end R1Z.ProverCommitTablePrefix21
