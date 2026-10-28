import R1Z.PV_RDB1_Pointer
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V187Iterator

/-- The ZST iterator end is an encoded byte count, never a dereference pointer.
Equality detects exactly zero remaining elements even when address arithmetic
wraps. This is a symbolic bitvector law, not an enumeration of machine words. -/
theorem zst_empty {width : Nat} (base count : BitVec width) :
    base + count = base ↔ count = 0#width := by
  constructor
  · intro h
    have hh := congrArg (fun x : BitVec width => x - base) h
    rw [BitVec.add_comm base count, BitVec.add_sub_cancel] at hh
    simpa only [BitVec.sub_self] using hh
  · intro h
    rw [h, BitVec.add_zero]

theorem zst_step {width : Nat} (base count : BitVec width) :
    (base + count) - 1#width = base + (count - 1#width) := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-- Sequential owned reads in from_fn order. acc models the initialized
prefix; the remaining list models IntoIter's live ownership region. -/
def fill {T : Type} : Nat → List T → List T → Result (List T × List T)
  | 0,remaining,acc => ok (acc,remaining)
  | _+1,[],_ => fail .panic
  | n+1,x::xs,acc => fill n xs (acc ++ [x])

theorem fill_exact {T : Type} (xs acc : List T) :
    fill xs.length xs acc = ok (acc ++ xs, []) := by
  induction xs generalizing acc with
  | nil => simp only [List.length_nil, fill, List.append_nil]
  | cons x xs ih =>
    simp only [List.length_cons, fill, ih, List.append_assoc, List.singleton_append]

theorem initialized_count {T : Type} (xs acc : List T) :
    (acc ++ xs).length = acc.length + xs.length := List.length_append

theorem next_bounds (initialized n : Nat) (h : initialized < n) :
    initialized + 1 ≤ n := by omega

/-- No live payload remains for destructor glue on a successful full drain;
all ownership has transferred in source order, for arbitrary non-Copy T. -/
theorem complete {T : Type} (xs : List T) :
    fill xs.length xs [] = ok (xs, []) := by
  simpa only [List.nil_append] using fill_exact xs []

#print axioms zst_empty
#print axioms zst_step
#print axioms fill_exact
#print axioms initialized_count
#print axioms next_bounds
#print axioms complete
end R1Z.PV_RDB1_V187Iterator
