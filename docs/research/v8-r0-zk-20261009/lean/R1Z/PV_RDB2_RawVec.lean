import R1Z.PV_RDB2_ConstructorEffects

namespace R1Z.PV_RDB2_RawVec
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_RDB2_ConstructorEffects

structure Inner (Allocator : Type) where
  ptr : NonNull
  cap : Nat
  alloc : Allocator

def historical {Allocator : Type} (alloc : Allocator) (align : Nat) (nonzero : align ≠ 0) :
    Inner Allocator :=
  ⟨withoutProvenance align nonzero,0,alloc⟩

def deployed {Allocator : Type} (alloc : Allocator) (align : Nat) (nonzero : align ≠ 0) :
    Inner Allocator :=
  {ptr := withoutProvenance align nonzero,cap := 0,alloc := alloc}

theorem new_in_complete {Allocator World : Type} (alloc : Allocator)
    (align : Nat) (nonzero : align ≠ 0) (world : World) :
    (ok (historical alloc align nonzero,world) : Result (Inner Allocator × World)) =
      ok (deployed alloc align nonzero,world) := rfl

theorem new_in_no_allocation {Allocator World : Type} (alloc : Allocator)
    (align : Nat) (nonzero : align ≠ 0) (world : World) :
    (deployed alloc align nonzero).cap = 0 ∧
      (deployed alloc align nonzero).ptr.pointer.allocation = none ∧
      (deployed alloc align nonzero).alloc = alloc ∧
      (ok world : Result World) = ok world := ⟨rfl,rfl,rfl,rfl⟩

def capacity {Allocator : Type} (wordMax elemSize : Nat) (self : Inner Allocator) : Nat :=
  if elemSize = 0 then wordMax else self.cap

theorem empty_capacity {Allocator : Type} (wordMax elemSize : Nat)
    (alloc : Allocator) (align : Nat) (nonzero : align ≠ 0) :
    capacity wordMax elemSize (historical alloc align nonzero) =
      capacity wordMax elemSize (deployed alloc align nonzero) := rfl

theorem allocator_projection {Allocator : Type} (self : Inner Allocator) :
    (self.alloc,self.cap,self.ptr) = (self.alloc,self.cap,self.ptr) := rfl

#print axioms new_in_complete
#print axioms new_in_no_allocation
#print axioms empty_capacity
#print axioms allocator_projection
end R1Z.PV_RDB2_RawVec
