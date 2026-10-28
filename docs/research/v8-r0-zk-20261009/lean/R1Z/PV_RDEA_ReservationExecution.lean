import R1Z.PV_RDEA_NameFill
import R1Z.PV_RDEA_CloneExecution
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_ReservationExecution
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath PV_RDEA_CapacityEndpoint

def run {S F : Type} (step : Request → S → Option Nat × S) (shape : Shape)
    (address : Nat) (digest : List (Fin 256)) (w : World S F) : Outcome (Buffer U8) S F :=
  let e := PV_RDB1_V181.deployed step 18446744073709551615 9223372036854775807 shape address 69 w
  match e.returned with
  | .error err => (Except.error err,e.world)
  | .ok () => PV_RDEA_NameFill.fill step shape digest e.buffer e.world

/-- Constructor plus all 65 source-ordered appends: one request, on failure
as well as success. Earlier private allocator state is unrestricted. -/
theorem requests {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat)
    (digest : List (Fin 256)) (length : digest.length=32) (w : World S F) :
    sizes (run step shape address digest w).2.history=sizes w.history++[(0,69,1)] := by
  let e := PV_RDB1_V181.deployed step 18446744073709551615 9223372036854775807 shape address 69 w
  have hist := literal_sizes step shape width address w
  change sizes e.world.history=_ at hist
  unfold run
  change sizes (match e.returned with
    | .error err => (Except.error err,e.world)
    | .ok () => PV_RDEA_NameFill.fill step shape digest e.buffer e.world).2.history=_
  cases h : e.returned with
  | error err => exact hist
  | ok unit =>
    have cap : e.buffer.capacity=69 := PV_RDEA_CloneExecution.capacity_success step shape address 69 w h
    have empty : e.buffer.values=[] := PV_RDB1_V181.empty_value step _ _ shape width address 69 w
    have fits : e.buffer.values.length+2*digest.length+5≤e.buffer.capacity := by rw [empty,length,cap]; simp only [List.length_nil]; omega
    obtain ⟨out,after,hr,_,_,_,_,hh,_⟩ := PV_RDEA_NameFill.complete step shape digest e.buffer e.world fits
    rw [hr]
    simpa only [hh] using hist

#print axioms requests
end R1Z.PV_RDEA_ReservationExecution
