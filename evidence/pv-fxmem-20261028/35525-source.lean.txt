import R1Z.PV_FXM_ReserveWorld
set_option autoImplicit false
namespace R1Z.PV_FXM_ReservePrimitive
open Aeneas Aeneas.Std PV_FXM_ReserveWorld

def layout (shape : Shape) (capacity : Nat) : core.alloc.layout.Layout :=
  ⟨usize (capacity*shape.width),shape.align⟩

/-- Exactly the Global runtime primitive signatures. A fresh allocation does
not receive the dangling old pointer or element count; same-align growth is
raw realloc with the old layout and requested new size. -/
def step {S : Type}
    (allocate : core.alloc.layout.Layout → S → Option Nat × S)
    (reallocate : Nat → core.alloc.layout.Layout → Usize → S → Option Nat × S)
    (r : Request) (s : S) : Option Nat × S :=
  if r.oldCapacity=0 then allocate (layout r.shape r.newCapacity) s else
    reallocate r.address (layout r.shape r.oldCapacity)
      (usize (r.newCapacity*r.shape.width)) s

theorem allocate_branch {S : Type}
    (allocate : core.alloc.layout.Layout → S → Option Nat × S)
    (reallocate : Nat → core.alloc.layout.Layout → Usize → S → Option Nat × S)
    (r : Request) (s : S) (h : r.oldCapacity=0) :
    step allocate reallocate r s=allocate (layout r.shape r.newCapacity) s := by
  simp only [step,h,ite_true]

theorem allocate_address_irrelevant {S : Type}
    (allocate : core.alloc.layout.Layout → S → Option Nat × S)
    (reallocate : Nat → core.alloc.layout.Layout → Usize → S → Option Nat × S)
    (r : Request) (s : S) (h : r.oldCapacity=0) (address : Nat) :
    step allocate reallocate {r with address := address} s=step allocate reallocate r s := by
  simp only [step,h,ite_true]

theorem realloc_branch {S : Type}
    (allocate : core.alloc.layout.Layout → S → Option Nat × S)
    (reallocate : Nat → core.alloc.layout.Layout → Usize → S → Option Nat × S)
    (r : Request) (s : S) (h : r.oldCapacity≠0) :
    step allocate reallocate r s=reallocate r.address (layout r.shape r.oldCapacity)
      (usize (r.newCapacity*r.shape.width)) s := by
  simp only [step,h,ite_false]

theorem exact_size (shape : Shape) (capacity : Nat)
    (h : capacity*shape.width<2^UScalarTy.Usize.numBits) :
    (layout shape capacity).size.val=capacity*shape.width := usize_exact _ h

theorem alignment (shape : Shape) (oldCap newCap : Nat) :
    (layout shape oldCap).align=(layout shape newCap).align := rfl

#print axioms allocate_branch
#print axioms allocate_address_irrelevant
#print axioms realloc_branch
#print axioms exact_size
#print axioms alignment
end R1Z.PV_FXM_ReservePrimitive
