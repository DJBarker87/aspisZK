import R1Z.PV_RDEA_ReservationExecution
import R1Z.PV_RDEA_SelectedCapacityConsumer
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_V181ConsumedLaw
open PV_RDB1_V183_ReserveWorld PV_RDEA_CapacityEndpoint

/-- Restated consumed row law. The returning arm is selected only after the
actual constructor Result; allocation error reaches the actual post-world
handler. No unconditional success or allocator-state equality is assumed. -/
theorem consumed {S F R : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat) (w : World S F)
    (failure : PV_RDB1_V183_ReserveWorld.Error → World S F → R)
    (next : Buffer U8 → World S F → R) :
    let e := PV_RDB1_V181.deployed step 18446744073709551615 9223372036854775807 shape address 69 w
    consume e failure next =
      (match e.returned with
       | .error err => failure err e.world
       | .ok () => next e.buffer e.world) ∧
      sizes e.world.history=sizes w.history++[(0,69,1)] := by
  exact ⟨rfl,literal_sizes step shape width address w⟩

/-- The complete fixed-name stage, including a failed constructor, has one
public-sized request. Request outcome still belongs to runtime/allocator
primitive adequacy; this theorem does not project away that outcome. -/
theorem name_stage {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat)
    (digest : List (Fin 256)) (length : digest.length=32) (w : World S F) :
    sizes (PV_RDEA_ReservationExecution.run step shape address digest w).2.history=
      sizes w.history++[(0,69,1)] :=
  PV_RDEA_ReservationExecution.requests step shape width address digest length w

#print axioms consumed
#print axioms name_stage
end R1Z.PV_RDEA_V181ConsumedLaw
