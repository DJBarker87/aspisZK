import R1Z.PV_RDCD4_Chunks194
namespace R1Z.PV_RDCD4_Split194
set_option autoImplicit false

/-- Ordered typed-memory interpretation of the two raw slices. The caller's
mid<=length proves their ranges valid. Pointer/layout semantics stay V370. -/
def unchecked {E : Type} (xs : List E) (mid : Nat) : List E × List E :=
  (xs.take mid,xs.drop mid)

def checked {E : Type} (xs : List E) (mid : Nat) : Option (List E × List E) :=
  if mid ≤ xs.length then some (unchecked xs mid) else none

theorem ranges {E : Type} (xs : List E) (mid : Nat) (h : mid ≤ xs.length) :
    (unchecked xs mid).1.length = mid ∧
    (unchecked xs mid).2.length = xs.length-mid ∧
    (unchecked xs mid).1 ++ (unchecked xs mid).2 = xs := by
  simp only [unchecked,List.length_take,List.length_drop,List.take_append_drop,
    Nat.min_eq_left h,and_self]

theorem success {E : Type} (xs : List E) (mid : Nat) (h : mid ≤ xs.length) :
    checked xs mid = some (xs.take mid,xs.drop mid) := by
  unfold checked
  rw [if_pos h]
  rfl

theorem failure {E : Type} (xs : List E) (mid : Nat) (h : xs.length < mid) :
    checked xs mid = none := by
  unfold checked
  rw [if_neg (by omega)]

/-- The source's Option.and_then store, retaining the original state on None. -/
def chunkSource {E : Type} (s : PV_RDCD4_Chunks194.State E) :=
  match checked s.v 2 with
  | none => (none,s)
  | some (chunk,rest) =>
    (some chunk, ({v := rest,rem := s.rem} : PV_RDCD4_Chunks194.State E))

theorem next_binding {E : Type} (s : PV_RDCD4_Chunks194.State E) :
    chunkSource s = PV_RDCD4_Chunks194.next s := by
  unfold chunkSource checked PV_RDCD4_Chunks194.next
  split <;> rfl

#print axioms ranges
#print axioms success
#print axioms failure
#print axioms next_binding
end R1Z.PV_RDCD4_Split194
