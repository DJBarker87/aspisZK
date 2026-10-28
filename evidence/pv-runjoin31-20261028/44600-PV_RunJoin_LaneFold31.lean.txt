import R1Z.PV_RunJoin_OuterExternal30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LaneFold31
open Aeneas Aeneas.Std Result
abbrev Digest := Array U32 8#usize

/-- Same two calls and operand order as the frozen lane-root branch. -/
def step (parent : Digest → Digest → Result Digest)
    (current sibling : Digest) (reverse : Bool) : Result Digest :=
  if reverse then parent sibling current else parent current sibling

theorem step_original (parent : Digest → Digest → Result Digest)
    (current sibling : Digest) (zero : Bool) :
    step parent current sibling (!zero) =
      (if zero then parent current sibling else parent sibling current) := by
  cases zero <;> rfl
#print axioms step_original

/-- Full Result recurrence. Neither errors nor failed prefixes are erased. -/
def fold (parent : Digest → Digest → Result Digest)
    (sibling : Nat → Digest) (reverse : Nat → Bool) : List Nat → Digest → Result Digest
  | [], current => ok current
  | level::levels, current => do
      let next ← step parent current (sibling level) (reverse level)
      fold parent sibling reverse levels next

theorem fold_append (parent : Digest → Digest → Result Digest)
    (sibling : Nat → Digest) (reverse : Nat → Bool)
    (xs ys : List Nat) (current : Digest) :
    fold parent sibling reverse (xs++ys) current =
      (do let mid ← fold parent sibling reverse xs current
          fold parent sibling reverse ys mid) := by
  induction xs generalizing current with
  | nil => rfl
  | cons level levels ih =>
    simp only [List.cons_append,fold]
    cases h : step parent current (sibling level) (reverse level) <;>
      simp only [bind_tc_ok,bind_tc_fail,bind_tc_div,ih]
#print axioms fold_append
end R1Z.PV_RunJoin_LaneFold31
