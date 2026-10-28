import R1Z.PV_RDB2C_Base_RawVec
namespace R1Z.PV_RDB2C_TypedRawVec
open Aeneas Aeneas.Std Result PV_RDB2_RawVec
structure Typed (T A : Type) where
  inner : Inner A
  marker : Unit

def historical {T A : Type} (allocator : A) (align : Nat) (h : align ≠ 0) : Typed T A :=
  ⟨PV_RDB2_RawVec.historical allocator align h,()⟩
def deployed {T A : Type} (allocator : A) (align : Nat) (h : align ≠ 0) : Typed T A :=
  {inner := PV_RDB2_RawVec.deployed allocator align h,marker := ()}

theorem complete {T A W : Type} (allocator : A) (align : Nat) (h : align ≠ 0) (world : W) :
    (ok (historical (T:=T) allocator align h,world) : Result (Typed T A × W)) =
      ok (deployed (T:=T) allocator align h,world) := rfl

theorem no_allocation {T A : Type} (allocator : A) (align : Nat) (h : align ≠ 0) :
    (deployed (T:=T) allocator align h).inner.cap = 0 ∧
    (deployed (T:=T) allocator align h).inner.ptr.pointer.allocation = none ∧
    (deployed (T:=T) allocator align h).inner.alloc = allocator := ⟨rfl,rfl,rfl⟩

theorem zst_capacity {T A : Type} (allocator : A) (align : Nat) (h : align ≠ 0) (wordMax : Nat) :
    capacity wordMax 0 (deployed (T:=T) allocator align h).inner = wordMax := rfl

theorem non_zst_capacity {T A : Type} (allocator : A) (align size : Nat)
    (h : align ≠ 0) (hs : size ≠ 0) (wordMax : Nat) :
    capacity wordMax size (deployed (T:=T) allocator align h).inner = 0 := by
  simp only [capacity,hs,ite_false,deployed,PV_RDB2_RawVec.deployed]

#print axioms complete
#print axioms no_allocation
#print axioms zst_capacity
#print axioms non_zst_capacity
end R1Z.PV_RDB2C_TypedRawVec
