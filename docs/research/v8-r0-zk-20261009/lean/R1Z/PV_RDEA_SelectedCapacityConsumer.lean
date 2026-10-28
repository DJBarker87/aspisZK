import R1Z.PV_RDEA_CapacityEndpoint
import R1Z.PV_CBL_CapacityValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDEA_SelectedCapacityConsumer
open PV_RDB1_V183_ReserveWorld

/-- Returning-value projection used by the existing selected callback. This
is applied only on the success arm of the error-aware native consumer. -/
def decode (b : Buffer U8) : Result String :=
  if b.values=[] then .ok "" else .fail .panic

theorem decoded_constructor {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address n : Nat) (u : Usize)
    (w : World S F) :
    decode (PV_RDB1_V181.deployed step 18446744073709551615
      9223372036854775807 shape address n w).buffer =
      PV_CBL_CapacityValue.reference u := by
  rw [PV_CBL_CapacityValue.value]
  simp only [decode,PV_RDB1_V181.empty_value step _ _ shape width,ite_true]

/-- Restated consumed law: failure calls the native handler with its actual
post-request world. Success consumes the historical selected callback's value
in that same world. The unconditional native-success law is superseded. -/
theorem consumed {S F R : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address n : Nat) (u : Usize)
    (w : World S F)
    (failure : PV_RDB1_V183_ReserveWorld.Error → World S F → Result R)
    (next : String → World S F → Result R) :
    let e := PV_RDB1_V181.deployed step 18446744073709551615
      9223372036854775807 shape address n w
    PV_RDEA_CapacityEndpoint.consume e failure
      (fun b world => do let value ← decode b; next value world) =
    (match e.returned with
    | .error err => failure err e.world
    | .ok () => do let value ← PV_CBL_CapacityValue.reference u; next value e.world) := by
  dsimp only
  unfold PV_RDEA_CapacityEndpoint.consume
  split
  · rfl
  · rw [decoded_constructor step shape width address n u w]

#print axioms decoded_constructor
#print axioms consumed
end R1Z.PV_RDEA_SelectedCapacityConsumer
