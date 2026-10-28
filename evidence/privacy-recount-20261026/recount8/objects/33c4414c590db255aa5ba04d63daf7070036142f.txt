import R1Z.PV_RDB2_ConstructorEffects

/-! The changed AtomicPtr constructor/load wrappers preserve the stored
pointer, cell address, ordering and complete underlying atomic operation.
The atomic primitive remains the same operation in both interpretations;
its scheduling semantics are not replaced by a constant pure read. -/
namespace R1Z.PV_RDB2_Atomic
set_option autoImplicit false
open Aeneas Aeneas.Std Result

structure Cell (T : Type) where
  address : Nat
  stored : T

structure AtomicPtr (T : Type) where
  p : Cell T

def oldNew {T : Type} (address : Nat) (pointer : T) : AtomicPtr T :=
  ⟨⟨address,pointer⟩⟩
def deployedNew {T : Type} (address : Nat) (pointer : T) : AtomicPtr T :=
  {p := {address := address,stored := pointer}}
def asPtr {T : Type} (self : AtomicPtr T) : Nat := self.p.address

def oldLoad {T World Order : Type}
    (atomicLoad : Nat → Order → World → Result (T × World))
    (self : AtomicPtr T) (order : Order) (world : World) : Result (T × World) :=
  atomicLoad (asPtr self) order world
def deployedLoad {T World Order : Type}
    (atomicLoad : Nat → Order → World → Result (T × World))
    (self : AtomicPtr T) (order : Order) (world : World) : Result (T × World) :=
  atomicLoad self.p.address order world

theorem new_complete {T World : Type} (address : Nat) (pointer : T) (world : World) :
    (ok (oldNew address pointer,world) : Result (AtomicPtr T × World)) =
      ok (deployedNew address pointer,world) := rfl

theorem load_complete {T World Order : Type}
    (atomicLoad : Nat → Order → World → Result (T × World))
    (self : AtomicPtr T) (order : Order) (world : World) :
    oldLoad atomicLoad self order world = deployedLoad atomicLoad self order world := rfl

theorem new_then_load {T World Order : Type}
    (atomicLoad : Nat → Order → World → Result (T × World))
    (address : Nat) (pointer : T) (order : Order) (world : World) :
    oldLoad atomicLoad (oldNew address pointer) order world =
      deployedLoad atomicLoad (deployedNew address pointer) order world := rfl

#print axioms new_complete
#print axioms load_complete
#print axioms new_then_load
end R1Z.PV_RDB2_Atomic
