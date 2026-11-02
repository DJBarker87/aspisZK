import PV_EVH_AllocatorWorld
set_option autoImplicit false
namespace PV_EVH_HeapOwnership
open PV_EVH_Runtime
open PV_RJ4IDB (Bytes)

/-- The key is independent of the extensional contents of a source value. -/
structure Key where
  identity : Nat
  owner : Nat
  deriving DecidableEq

/-- A byte-vector view records its initialized prefix separately from capacity.
The codec from typed source elements is a further native association obligation. -/
structure View where
  key : Key
  contents : Bytes
  capacity : Nat

/-- Ownership is exclusive by allocation identity, including equal-valued Vecs. -/
def UniqueHeap (heap : List Block) : Prop :=
  ∀ b ∈ heap, ∀ c ∈ heap, b.identity = c.identity → b = c

def Owns (heap : List Block) (v : View) (b : Block) : Prop :=
  b ∈ heap ∧ b.identity = v.key.identity ∧ b.owner = v.key.owner ∧
  b.layout.size = v.capacity ∧ b.bytes.length = v.capacity ∧
  v.contents.length ≤ v.capacity ∧ b.bytes.take v.contents.length = v.contents

theorem ownership_selects_identity (heap : List Block) (v : View) (b c : Block)
    (hu : UniqueHeap heap) (hb : Owns heap v b) (hc : Owns heap v c) : b = c :=
  hu b hb.1 c hc.1 (hb.2.1.trans hc.2.1.symm)

theorem different_keys_cannot_share (heap : List Block) (v u : View) (b : Block)
    (hv : Owns heap v b) (hu : Owns heap u b) : v.key = u.key := by
  cases v with
  | mk vk vc vn =>
    cases u with
    | mk uk uc un =>
      cases vk with
      | mk vi vo =>
        cases uk with
        | mk ui uo =>
          have hi := hv.2.1.symm.trans hu.2.1
          have ho := hv.2.2.1.symm.trans hu.2.2.1
          cases hi
          cases ho
          rfl

/-- The token retains the exact pre-borrow allocation and suspended owner. -/
structure Borrow where
  key : Key
  before : Block
  identity_eq : before.identity = key.identity
  owner_eq : before.owner = key.owner

/-- Restoration accepts the same identity and owner, not contents equality. -/
def Restores (loan : Borrow) (after : Block) : Prop :=
  after.identity = loan.key.identity ∧ after.owner = loan.key.owner ∧
  after.address = loan.before.address ∧ after.layout = loan.before.layout

theorem restore_keeps_address (loan : Borrow) (after : Block) (h : Restores loan after) :
    after.address = loan.before.address := h.2.2.1

theorem restore_rejects_other_owner (loan : Borrow) (after : Block)
    (h : after.owner ≠ loan.key.owner) : ¬ Restores loan after := by
  intro hr
  exact h hr.2.1

/-- Installing a new block preserves old ownership when its identity is fresh. -/
theorem allocation_preserves_ownership (heap : List Block) (v : View) (b fresh : Block)
    (h : Owns heap v b) : Owns (fresh :: heap) v b :=
  ⟨List.mem_cons_of_mem fresh h.1,h.2⟩

theorem fresh_allocation_unique (heap : List Block) (fresh : Block)
    (hu : UniqueHeap heap) (hf : ∀ b ∈ heap, b.identity ≠ fresh.identity) :
    UniqueHeap (fresh :: heap) := by
  intro b hb c hc hi
  rcases List.mem_cons.mp hb with hb | hb
  · subst b
    rcases List.mem_cons.mp hc with hc | hc
    · exact hc.symm
    · exact False.elim (hf c hc hi.symm)
  · rcases List.mem_cons.mp hc with hc | hc
    · subst c
      exact False.elim (hf b hb hi)
    · exact hu b hb c hc hi

#print axioms ownership_selects_identity
#print axioms different_keys_cannot_share
#print axioms restore_keeps_address
#print axioms restore_rejects_other_owner
#print axioms allocation_preserves_ownership
#print axioms fresh_allocation_unique
end PV_EVH_HeapOwnership
