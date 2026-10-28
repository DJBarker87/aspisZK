import R1Z.PV_RDB2C_Base_GlobalAlloc

/-! Truncate's destructor is an effectful complete-result parameter. The
length write precedes that call, including when destruction panics. Keeping
the world outside Result records this ordering on the error path as well. -/
namespace R1Z.PV_RDB2_Truncate
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_RDB2_ConstructorEffects

structure Vec (Allocator : Type) where
  ptr : Raw
  length : Nat
  capacity : Nat
  allocator : Allocator

def tail (ptr : Raw) (elementSize start count : Nat) : Raw :=
  {ptr with address := ptr.address+elementSize*start,metadata := some count}

def oldTail (ptr : Raw) (elementSize start count : Nat) : Raw :=
  PV_RDB2_GlobalAlloc.castSlice {ptr with address := ptr.address+elementSize*start} count

def oldTruncate {Allocator World : Type}
    (drop : Raw → Vec Allocator → World → Result Unit × Vec Allocator × World)
    (elementSize n : Nat) (self : Vec Allocator) (world : World) :=
  if n > self.length then (ok (),self,world)
  else drop (oldTail self.ptr elementSize n (self.length-n)) {self with length := n} world

def deployedTruncate {Allocator World : Type}
    (drop : Raw → Vec Allocator → World → Result Unit × Vec Allocator × World)
    (elementSize n : Nat) (self : Vec Allocator) (world : World) :=
  if n > self.length then (ok (),self,world)
  else drop (tail self.ptr elementSize n (self.length-n)) {self with length := n} world

theorem complete {Allocator World : Type}
    (drop : Raw → Vec Allocator → World → Result Unit × Vec Allocator × World)
    (elementSize n : Nat) (self : Vec Allocator) (world : World) :
    oldTruncate drop elementSize n self world = deployedTruncate drop elementSize n self world := rfl

theorem reduced_before_drop {Allocator World : Type}
    (drop : Raw → Vec Allocator → World → Result Unit × Vec Allocator × World)
    (elementSize n : Nat) (self : Vec Allocator) (world : World) (h : n ≤ self.length) :
    deployedTruncate drop elementSize n self world =
      drop (tail self.ptr elementSize n (self.length-n)) {self with length := n} world := by
  exact if_neg (by omega)

theorem no_drop_when_extending {Allocator World : Type}
    (drop : Raw → Vec Allocator → World → Result Unit × Vec Allocator × World)
    (elementSize n : Nat) (self : Vec Allocator) (world : World) (h : self.length < n) :
    deployedTruncate drop elementSize n self world = (ok (),self,world) := if_pos h

#print axioms complete
#print axioms reduced_before_drop
#print axioms no_drop_when_extending
end R1Z.PV_RDB2_Truncate
