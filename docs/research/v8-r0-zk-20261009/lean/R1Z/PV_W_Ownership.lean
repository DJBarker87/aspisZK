import R1Z.PV_W_Enriched
set_option autoImplicit false
namespace R1Z.PV_W_Ownership

/-- A generation distinguishes reuse of one descriptor/address. The source
value list or integer descriptor alone does not carry this ownership token. -/
structure Token where
  address : Nat
  generation : Nat
  deriving DecidableEq

abbrev Slots := Nat → Option Token

def take (slot : Nat) (s : Slots) : Option Token × Slots :=
  (s slot,fun i => if i=slot then none else s i)

def Unique (s : Slots) : Prop :=
  ∀ i j t, s i=some t → s j=some t → i=j

theorem take_source (slot : Nat) (s : Slots) : (take slot s).1=s slot := rfl

theorem take_empty (slot : Nat) (s : Slots) : (take slot s).2 slot=none := by
  simp only [take,ite_true]

theorem take_other (slot i : Nat) (s : Slots) (h : i≠slot) :
    (take slot s).2 i=s i := by simp only [take,h,ite_false]

theorem take_twice (slot : Nat) (s : Slots) :
    (take slot (take slot s).2).1=none := take_empty slot s

theorem take_unique (slot : Nat) (s : Slots) (h : Unique s) : Unique (take slot s).2 := by
  intro i j t hi hj
  have ni : i≠slot := by intro eq; subst i; rw [take_empty] at hi; cases hi
  have nj : j≠slot := by intro eq; subst j; rw [take_empty] at hj; cases hj
  rw [take_other slot i s ni] at hi
  rw [take_other slot j s nj] at hj
  exact h i j t hi hj

/-- Local scope exit consumes the slot before invoking glue. An empty slot
runs no glue. Failure/unwind semantics of glue are separately interpreted. -/
def dropSlot {S : Type} (glue : Token → S → S) (slot : Nat) (s : Slots) (w : S) : Slots × S :=
  let r := take slot s
  (r.2,match r.1 with | none => w | some t => glue t w)

theorem drop_slot_empty {S : Type} (glue : Token → S → S) (slot : Nat) (s : Slots)
    (w : S) (h : s slot=none) : (dropSlot glue slot s w).2=w := by
  simp only [dropSlot,take,h]

theorem drop_slot_once {S : Type} (glue : Token → S → S) (slot : Nat) (s : Slots)
    (w : S) (t : Token) (h : s slot=some t) :
    (dropSlot glue slot s w).2=glue t w ∧
      (dropSlot glue slot (dropSlot glue slot s w).1 (dropSlot glue slot s w).2).2=glue t w := by
  have one : (dropSlot glue slot s w).2=glue t w := by simp only [dropSlot,take,h]
  refine ⟨one,?_⟩
  exact (drop_slot_empty glue slot (dropSlot glue slot s w).1
    (dropSlot glue slot s w).2 (take_empty slot s)).trans one

theorem drop_slot_unique {S : Type} (glue : Token → S → S) (slot : Nat) (s : Slots)
    (w : S) (h : Unique s) : Unique (dropSlot glue slot s w).1 := take_unique slot s h

#print axioms take_source
#print axioms take_empty
#print axioms take_other
#print axioms take_twice
#print axioms take_unique
#print axioms drop_slot_empty
#print axioms drop_slot_once
#print axioms drop_slot_unique
end R1Z.PV_W_Ownership
