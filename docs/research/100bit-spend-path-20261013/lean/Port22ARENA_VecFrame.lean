import Port22ARENA_Bump

/-! Dependent byte-frame consequence for the exact fresh RawVec write sites.
The field-address/unsafe native interpretation remains explicit, not installed.
No post-length or whole-helper equality is a hypothesis. -/
set_option autoImplicit false
namespace Port22ARENA

def readLE (mem : Memory) (base : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => mem base + 256 * readLE mem (base+1) n

def Separated (x y : Nat) : Prop := x+8 ≤ y ∨ y+8 ≤ x

theorem readLE_congr (m m' : Memory) (base count : Nat)
    (same : ∀ x, base ≤ x → x < base+count → m x = m' x) :
    readLE m base count = readLE m' base count := by
  induction count generalizing base with
  | zero => rfl
  | succ n ih =>
    simp only [readLE]
    rw [same base (by omega) (by omega)]
    rw [ih (base+1) (by intro x lo hi; apply same x <;> omega)]

theorem store_length_frame (mem : Memory) (address value lengthAddress : Nat)
    (disjoint : Separated address lengthAddress) :
    readLE (storeCursor mem address value) lengthAddress 8 =
      readLE mem lengthAddress 8 := by
  apply readLE_congr
  intro x lo hi
  apply store_outside
  unfold Separated at disjoint
  omega

/-- Only the cursor then ptr/cap stores in this fresh non-reallocation cone. -/
def stores (mem : Memory) : List (Nat × Nat) → Memory
  | [] => mem
  | (address,value)::rest => stores (storeCursor mem address value) rest

theorem stores_length_frame (mem : Memory) (writes : List (Nat × Nat))
    (lengthAddress : Nat)
    (disjoint : ∀ w ∈ writes, Separated w.1 lengthAddress) :
    readLE (stores mem writes) lengthAddress 8 = readLE mem lengthAddress 8 := by
  induction writes generalizing mem with
  | nil => rfl
  | cons w rest ih =>
    simp only [stores]
    rw [ih (storeCursor mem w.1 w.2) (by
      intro v hv
      exact disjoint v (List.mem_cons_of_mem w hv))]
    exact store_length_frame mem w.1 w.2 lengthAddress
      (disjoint w (List.mem_cons_self))

/-- Exact admitted store addresses, not an assumed post-Vec frame.
The prefix includes pre-allocation error, null, partial store, and full stores;
classification of actual abort cuts is an independent native obligation. -/
theorem fresh_reserve_length (mem : Memory)
    (arena ptrField capField lenField pointer capacity count : Nat)
    (arenaApart : Separated arena lenField)
    (ptrApart : Separated ptrField lenField)
    (capApart : Separated capField lenField) :
    readLE (stores mem
      ([(arena,pointer),(ptrField,pointer),(capField,capacity)].take count)) lenField 8 =
      readLE mem lenField 8 := by
  apply stores_length_frame
  intro w hw
  have hm := List.mem_of_mem_take hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h
  · subst w; exact arenaApart
  · subst w; exact ptrApart
  · subst w; exact capApart

/-- The initialized range is derived from the unchanged zero len, on all cuts.
No contents/capacity or oracle-effect property is inferred from a Rust type. -/
theorem fresh_reserve_empty (mem : Memory)
    (arena ptrField capField lenField pointer capacity count : Nat)
    (arenaApart : Separated arena lenField)
    (ptrApart : Separated ptrField lenField)
    (capApart : Separated capField lenField)
    (fresh : readLE mem lenField 8 = 0) :
    ∀ index, ¬ index < readLE (stores mem
      ([(arena,pointer),(ptrField,pointer),(capField,capacity)].take count)) lenField 8 := by
  rw [fresh_reserve_length mem arena ptrField capField lenField pointer capacity count
    arenaApart ptrApart capApart, fresh]
  intro index
  omega

#print axioms readLE_congr
#print axioms store_length_frame
#print axioms stores_length_frame
#print axioms fresh_reserve_length
#print axioms fresh_reserve_empty
end Port22ARENA
