import Aeneas
set_option autoImplicit false
namespace KSE
/-- Logical slots, not addresses: covers zero-sized elements too. The backing
memory is retained in full; only the unconsumed half-open interval shrinks. -/
structure Cursor (T : Type) where
  lo : Nat
  hi : Nat
  mem : Nat → T

def write {T : Type} (m : Nat → T) (i : Nat) (v : T) : Nat → T :=
  fun j => if j = i then v else m j

def takeSlot {T : Type} (back : Bool) (s : Cursor T) : Option (Nat × Cursor T) :=
  if s.lo < s.hi then
    if back then some (s.hi - 1, {s with hi := s.hi - 1})
    else some (s.lo, {s with lo := s.lo + 1})
  else none

/-- The callback supplies the last value written through the yielded reference.
A finite schedule also models an early exit or the completed prefix of unwind. -/
def run {T : Type} (f : Nat → T → T) : List Bool → Cursor T → Cursor T × List (Nat × T)
  | [], s => (s, [])
  | d :: ds, s => match takeSlot d s with
    | none => (s, [])
    | some (i, next) =>
      let v := f i (s.mem i)
      let (out, log) := run f ds {next with mem := write s.mem i v}
      (out, (i,v) :: log)

def applyWrites {T : Type} : (Nat → T) → List (Nat × T) → (Nat → T)
  | m, [] => m
  | m, (i,v) :: xs => applyWrites (write m i v) xs

theorem selected_bounds {T : Type} (d : Bool) (s t : Cursor T) (i : Nat)
    (h : takeSlot d s = some (i,t)) :
    s.lo ≤ i ∧ i < s.hi ∧ s.lo ≤ t.lo ∧ t.hi ≤ s.hi ∧
      (∀ j, t.lo ≤ j → j < t.hi → j ≠ i) ∧ t.mem = s.mem := by
  unfold takeSlot at h
  split at h
  next nonempty =>
    split at h
    · cases h
      dsimp
      refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩ <;> intros <;> omega
    · cases h
      dsimp
      refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩ <;> intros <;> omega
  next => cases h

theorem trace_bounds {T : Type} (f : Nat → T → T) (ds : List Bool) (s : Cursor T) :
    ∀ p ∈ (run f ds s).2, s.lo ≤ p.1 ∧ p.1 < s.hi := by
  induction ds generalizing s with
  | nil => simp [run]
  | cons d ds ih =>
    simp only [run]
    cases h : takeSlot d s with
    | none => simp
    | some pair =>
      rcases pair with ⟨i,t⟩
      have b := selected_bounds d s t i h
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨b.1,b.2.1⟩
      · have q := ih {t with mem := write s.mem i (f i (s.mem i))} p hp
        exact ⟨Nat.le_trans b.2.2.1 q.1, Nat.lt_of_lt_of_le q.2 b.2.2.2.1⟩

theorem no_duplicate_yields {T : Type} (f : Nat → T → T) (ds : List Bool) (s : Cursor T) :
    ((run f ds s).2.map Prod.fst).Nodup := by
  induction ds generalizing s with
  | nil => simp [run]
  | cons d ds ih =>
    simp only [run]
    cases h : takeSlot d s with
    | none => simp
    | some pair =>
      rcases pair with ⟨i,t⟩
      have b := selected_bounds d s t i h
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        rcases List.mem_map.mp hm with ⟨p,hp,eq⟩
        have q := trace_bounds f ds {t with mem := write s.mem i (f i (s.mem i))} p hp
        exact b.2.2.2.2.1 p.1 q.1 q.2 eq
      · exact ih _

/-- Full restoration: every completed write, in yield order, and no truncation.
The original borrowed slice is obtained by taking its original length in mem. -/
theorem restoration {T : Type} (f : Nat → T → T) (ds : List Bool) (s : Cursor T) :
    (run f ds s).1.mem = applyWrites s.mem (run f ds s).2 := by
  induction ds generalizing s with
  | nil => rfl
  | cons d ds ih =>
    simp only [run]
    cases h : takeSlot d s with
    | none => rfl
    | some pair =>
      rcases pair with ⟨i,t⟩
      exact ih {t with mem := write s.mem i (f i (s.mem i))}

theorem untouched {T : Type} (m : Nat → T) (xs : List (Nat × T)) (j : Nat)
    (h : j ∉ xs.map Prod.fst) : applyWrites m xs j = m j := by
  induction xs generalizing m with
  | nil => rfl
  | cons p xs ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [applyWrites, ih _ h.2]
    simp [write, h.1]

def snapshot {T : Type} (n : Nat) (m : Nat → T) : List T := (List.range n).map m

theorem restored_slice {T : Type} (f : Nat → T → T) (ds : List Bool)
    (s : Cursor T) (originalLength : Nat) :
    snapshot originalLength (run f ds s).1.mem =
      snapshot originalLength (applyWrites s.mem (run f ds s).2) := by
  rw [restoration]

#print axioms selected_bounds
#print axioms trace_bounds
#print axioms no_duplicate_yields
#print axioms restoration
#print axioms untouched
#print axioms restored_slice
end KSE
