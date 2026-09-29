import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-! Exact flattened transcript framing. Addresses are bytes, not a disjoint
sum that would silently exclude other users of the shared oracle. -/
set_option autoImplicit false
namespace AspisV8R19.DuplexFrames
abbrev Byte := Fin 256
abbrev Bytes := List Byte
def squeeze (s : Bytes) : Bytes := s ++ [1]
def advance (s : Bytes) : Bytes := s ++ [2]
def absorb (s : Bytes) (label : Byte) (data : Bytes) : Bytes := s ++ [0, label] ++ data
def grind (s nonce : Bytes) : Bytes := s ++ [3] ++ nonce
def Fresh (reads : List Bytes) (s : Bytes) : Prop :=
  squeeze s ∉ reads ∧ advance s ∉ reads
def BadState (reads : List Bytes) (s : Bytes) : Prop :=
  ∃ p ∈ reads, p = squeeze s ∨ p = advance s

theorem squeeze_injective : Function.Injective squeeze := by
  intro s t h
  exact List.append_cancel_right h

theorem advance_injective : Function.Injective advance := by
  intro s t h
  exact List.append_cancel_right h

theorem cross_disjoint (s t : Bytes) : squeeze s ≠ advance t := by
  intro h
  have hh := congrArg List.getLast? h
  simp [squeeze, advance] at hh

theorem pair_collision_iff (s t : Bytes) :
    (squeeze s = squeeze t ∨ squeeze s = advance t ∨
      advance s = squeeze t ∨ advance s = advance t) ↔ s = t := by
  constructor
  · intro h
    rcases h with h | h | h | h
    · exact squeeze_injective h
    · exact (cross_disjoint s t h).elim
    · exact (cross_disjoint t s h.symm).elim
    · exact advance_injective h
  · rintro rfl; exact Or.inl rfl

theorem fresh_iff (reads : List Bytes) (s : Bytes) :
    Fresh reads s ↔ ¬ BadState reads s := by
  simp only [Fresh, BadState, not_exists, not_and, not_or]
  constructor
  · rintro ⟨hs, ha⟩ p hp
    exact ⟨fun h => hs (h ▸ hp), fun h => ha (h ▸ hp)⟩
  · intro h
    exact ⟨fun hs => (h _ hs).1 rfl, fun ha => (h _ ha).2 rfl⟩

theorem fresh_after_pair (reads : List Bytes) (s t : Bytes) :
    Fresh (reads ++ [squeeze s, advance s]) t ↔ Fresh reads t ∧ t ≠ s := by
  simp only [Fresh, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    not_or]
  constructor
  · rintro ⟨⟨ht, hts, _⟩, ha, _, _⟩
    exact ⟨⟨ht, ha⟩, fun h => hts (congrArg squeeze h)⟩
  · rintro ⟨⟨ht, ha⟩, hne⟩
    exact ⟨⟨ht, fun h => hne (squeeze_injective h), cross_disjoint t s⟩,
      ha, fun h => cross_disjoint s t h.symm, fun h => hne (advance_injective h)⟩

theorem absorb_disjoint (s t : Bytes) (hs : s.length = 32) (ht : t.length = 32)
    (label : Byte) (data : Bytes) :
    squeeze s ≠ absorb t label data ∧ advance s ≠ absorb t label data := by
  constructor <;> intro h <;> have hh := congrArg List.length h <;>
    simp [squeeze, advance, absorb, hs, ht] at hh <;> omega

theorem grind_disjoint (s t nonce : Bytes) (hs : s.length = 32)
    (ht : t.length = 32) (hn : nonce.length = 8) :
    squeeze s ≠ grind t nonce ∧ advance s ≠ grind t nonce := by
  constructor <;> intro h <;> have hh := congrArg List.length h <;>
    simp [squeeze, advance, grind, hs, ht, hn] at hh

theorem repeated_state_not_fresh (reads : List Bytes) (s : Bytes) :
    ¬ Fresh (reads ++ [squeeze s, advance s]) s := by
  rw [fresh_after_pair]; simp

#print axioms squeeze_injective
#print axioms advance_injective
#print axioms cross_disjoint
#print axioms pair_collision_iff
#print axioms fresh_iff
#print axioms fresh_after_pair
#print axioms absorb_disjoint
#print axioms grind_disjoint
#print axioms repeated_state_not_fresh
end AspisV8R19.DuplexFrames
