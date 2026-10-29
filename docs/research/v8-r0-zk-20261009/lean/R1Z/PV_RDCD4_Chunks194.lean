import Aeneas
namespace R1Z.PV_RDCD4_Chunks194
set_option autoImplicit false

/-- Value representation of the deployed ChunksExact fields at chunk_size=2.
References are represented by their ordered elements. Raw memory/layout remains V370. -/
structure State (E : Type) where
  v : List E
  rem : List E
  deriving Repr

def new {E : Type} (xs : List E) : State E :=
  let n := xs.length - xs.length % 2
  ⟨xs.take n, xs.drop n⟩

/-- split_at_checked then and_then, with the store to v only in Some. -/
def next {E : Type} (s : State E) : Option (List E) × State E :=
  if 2 ≤ s.v.length then
    (some (s.v.take 2), ⟨s.v.drop 2, s.rem⟩)
  else (none, s)

theorem new_even {E : Type} (xs : List E) (h : xs.length % 2 = 0) :
    new xs = ⟨xs, []⟩ := by
  simp only [new, h, Nat.sub_zero, List.take_length, List.drop_length]

theorem next_pair {E : Type} (a b : E) (tail rem : List E) :
    next (⟨a :: b :: tail, rem⟩ : State E) =
      (some [a,b], ⟨tail,rem⟩) := by
  simp only [next, List.length_cons, show 2 ≤ tail.length+1+1 by omega,
    if_pos, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]

theorem next_empty {E : Type} (rem : List E) :
    next (⟨[],rem⟩ : State E) = (none,⟨[],rem⟩) := by
  simp only [next, List.length_nil, show ¬2 ≤ 0 by omega, if_neg]

theorem next_single {E : Type} (a : E) (rem : List E) :
    next (⟨[a],rem⟩ : State E) = (none,⟨[a],rem⟩) := by
  simp only [next, List.length_cons, List.length_nil, show ¬2 ≤ 0+1 by omega, if_neg]

theorem message_new {E : Type} (xs : List E) (h : xs.length = 1024) :
    new xs = ⟨xs,[]⟩ := by
  apply new_even
  rw [h]

#print axioms new_even
#print axioms next_pair
#print axioms next_empty
#print axioms next_single
#print axioms message_new
end R1Z.PV_RDCD4_Chunks194
