import R1Z.PV_RDB1_V181
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDEA_V181
open PV_RDB1_V183_ReserveWorld
/-- Literal argument in reservation_path, checked against Rust and its emission
by source-check.py. This is not a bound on arbitrary with_capacity callers. -/
def reservationCapacity : Nat := 69

theorem reachable_bound : reservationCapacity < 9223372036854775807 := by
  unfold reservationCapacity
  omega

/-- The literal ledger call reaches allocation, never capacity overflow.
Allocation failure remains an error with its allocator world. -/
theorem reachable_constructor {S F : Type}
    (step : Request → S → Option Nat × S) (shape : Shape)
    (width : shape.width=1) (address : Nat) (w : World S F) :
    PV_RDB1_V181.deployed step 18446744073709551615 9223372036854775807
      shape address reservationCapacity w =
    finish step shape (PV_RDB1_V181.empty address) reservationCapacity w := by
  simp only [PV_RDB1_V181.deployed,reservationCapacity,width,Nat.mul_one]
  split <;> (try omega)
  split <;> (try omega)
  rfl

/-- Complete error/world law through an arbitrary consumer. The consumer is
passed the Execution, including its error and world, rather than empty bytes. -/
theorem consumer {S F R : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat) (w : World S F)
    (consume : Execution U8 S F → Result R) :
    consume (PV_RDB1_V181.deployed step 18446744073709551615
      9223372036854775807 shape address reservationCapacity w) =
    consume (PV_RDB1_V181.reference step 18446744073709551615
      9223372036854775807 shape address reservationCapacity w) :=
  PV_RDB1_V181.with_handlers step _ _ shape width address reservationCapacity w consume

/-- Even on the source-derived bounded domain, unconditional success is false.
This is an allocator-model obstruction, not a witnessed secret-dependent abort. -/
theorem null_allocator_rejects {S F : Type} (shape : Shape)
    (width : shape.width=1) (address : Nat) (w : World S F) :
    (PV_RDB1_V181.deployed (fun _ s => (none,s))
      18446744073709551615 9223372036854775807
      shape address reservationCapacity w).returned ≠ .ok () := by
  rw [reachable_constructor _ shape width]
  simp [finish]

#print axioms reachable_bound
#print axioms reachable_constructor
#print axioms consumer
#print axioms null_allocator_rejects
end R1Z.PV_RDEA_V181
