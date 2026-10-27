import R1Z.PV_CBL_VectorPopSpec
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_PopWorld
set_option autoImplicit false

/-- Allocation observations are retained, including pre-existing history. -/
structure World where
  alloc : Nat
  realloc : Nat
  dealloc : Nat
  history : List Nat
  deriving DecidableEq

/-- Native buffer identity and capacity are carried independently of values. -/
structure Buffer (T : Type) where
  address : Nat
  capacity : Nat
  value : alloc.vec.Vec T
  fits : value.val.length ≤ capacity

def after {T : Type} (b : Buffer T) : Buffer T :=
  ⟨b.address,b.capacity,(PV_CBL_VectorPopSpec.pop b.value).2,by
    rw [PV_CBL_VectorPopSpec.length]
    exact le_trans (Nat.sub_le _ _) b.fits⟩

def reference {T : Type} (b : Buffer T) (w : World) :
    Result (Option T × Buffer T × World) :=
  ok ((PV_CBL_VectorPopSpec.pop b.value).1,after b,w)

theorem complete {T : Type} (b : Buffer T) (w : World) :
    reference b w = ok (b.value.val.getLast?,after b,w) := rfl

theorem retains_buffer {T : Type} (b : Buffer T) :
    (after b).address=b.address ∧ (after b).capacity=b.capacity := ⟨rfl,rfl⟩

theorem remaining {T : Type} (b : Buffer T) :
    (after b).value.val=b.value.val.dropLast := rfl

theorem zero_allocations {T : Type} (b : Buffer T) (w : World) :
    ∃ r b', reference b w=ok (r,b',w) := ⟨_,_,rfl⟩

theorem nonvacuous {T : Type} (v : alloc.vec.Vec T) (address : Nat) :
    ∃ b : Buffer T, b.value=v ∧ b.address=address :=
  ⟨⟨address,v.val.length,v,le_refl _⟩,rfl,rfl⟩

#print axioms after
#print axioms reference
#print axioms complete
#print axioms retains_buffer
#print axioms remaining
#print axioms zero_allocations
#print axioms nonvacuous
end R1Z.PV_AL_PopWorld
