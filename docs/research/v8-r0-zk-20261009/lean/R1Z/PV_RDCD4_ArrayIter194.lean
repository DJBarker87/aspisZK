import Aeneas
namespace R1Z.PV_RDCD4_ArrayIter194
set_option autoImplicit false

/-- Initialized backing storage and IndexRange alive fields. The lifetime,
ManuallyDrop wrapper and transparent casts retain their V370 interpretation. -/
structure State (E : Type) where
  data : List E
  start : Nat
  stop : Nat
  deriving Repr

def valid {E : Type} (s : State E) : Prop :=
  s.start ≤ s.stop ∧ s.stop ≤ s.data.length

def new {E : Type} (xs : List E) : State E := ⟨xs,0,xs.length⟩

/-- IndexRange::next stores start+1 before the initialized element is read.
The None from getElem? is impossible for valid active states. -/
def next {E : Type} (s : State E) : Option E × State E :=
  if 0 < s.stop - s.start then
    (s.data[s.start]?, {s with start := s.start + 1})
  else (none,s)

theorem new_valid {E : Type} (xs : List E) : valid (new xs) := by
  exact ⟨Nat.zero_le _,Nat.le_refl _⟩

theorem next_done {E : Type} (s : State E) (h : s.start = s.stop) :
    next s = (none,s) := by
  simp only [next,h,Nat.sub_self, Nat.lt_irrefl,if_neg]

theorem next_active {E : Type} (s : State E) (h : valid s)
    (active : s.start < s.stop) :
    ∃ x, s.data[s.start]? = some x ∧
      next s = (some x,{s with start := s.start+1}) ∧
      valid {s with start := s.start+1} := by
  have bound : s.start < s.data.length := by obtain ⟨_,h⟩ := h; omega
  refine ⟨s.data[s.start], List.getElem?_eq_getElem bound, ?_, ?_⟩
  · simp only [next,show 0 < s.stop-s.start by omega,if_pos,
      List.getElem?_eq_getElem bound]
  · exact ⟨by dsimp; omega,h.2⟩

/-- Copy elements have no destructor; IntoIter::drop's needs_drop branch is false. -/
def dropCopy {E : Type} (_ : State E) : Unit := ()

theorem drop_copy {E : Type} (s : State E) : dropCopy s = () := rfl

#print axioms new_valid
#print axioms next_done
#print axioms next_active
#print axioms drop_copy
end R1Z.PV_RDCD4_ArrayIter194
