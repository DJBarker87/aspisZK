import R1Z.PV_RDEAC_AfterCapacity
import R1Z.PV_RDEA_V181ConsumedLaw
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDEAC_ConstructorSimulation
open PV_RDB1_V183_ReserveWorld PV_RDEAC_AppendSimulation PV_CBL_StringBytesAdapter
open PV_RDEAC_NameText PV_RDEAC_AfterCapacity PV_RDEA_CapacityEndpoint
variable [ExternalTypes]

theorem simulation {S F : Type} (ops : ExternalFuns)
    (step : Request → S → Option Nat × S) (shape : Shape) (width : shape.width=1)
    (address : Nat) (self : PV_RDEA_ActualReservationTail.Store)
    (digest : Array U8 32#usize) (w : World S F) :
    letI : ExternalFuns := PV_CBL_AppendSource.selected ops
    let e := PV_RDB1_V181.deployed step 18446744073709551615 9223372036854775807 shape address 69 w
    let run := PV_RDEA_ReservationExecution.run step shape address (digest.val.map PV_RDEAC_NibbleModel.byte) w
    sizes run.2.history=sizes w.history++[(0,69,1)] ∧
    (match e.returned with
     | .error err => run=(.error err,e.world)
     | .ok () => ∃ out after,run=(.ok out,after) ∧
       PV_RDEA_ActualEndpointConsumer.afterCapacity self digest ""=joinTail ops self (basenameText digest.val) ∧
       Represents (basenameText digest.val) out ∧ out.capacity=69 ∧
       out.address=e.buffer.address ∧ after.allocator=e.world.allocator ∧
       after.history=e.world.history ∧ after.frame=e.world.frame) := by
  letI : ExternalFuns := PV_CBL_AppendSource.selected ops
  dsimp only
  let e := PV_RDB1_V181.deployed step 18446744073709551615 9223372036854775807 shape address 69 w
  have empty : e.buffer.values=[] := PV_RDB1_V181.empty_value step _ _ shape width address 69 w
  have length : (digest.val.map PV_RDEAC_NibbleModel.byte).length=32 := by
    rw [List.length_map];exact digest.property
  refine ⟨PV_RDEA_ReservationExecution.requests step shape width address _ length w,?_⟩
  change (match e.returned with | .error err => _ | .ok () => _)
  cases h : e.returned with
  | error err =>
    unfold PV_RDEA_ReservationExecution.run
    change (match e.returned with | .error err => ((Except.error err : Except PV_RDB1_V183_ReserveWorld.Error (Buffer U8)),e.world) | .ok () => _) = _
    rw [h]
  | ok unit =>
    have cap : e.buffer.capacity=69 := PV_RDEA_CloneExecution.capacity_success step shape address 69 w h
    have repr : Represents "" e.buffer := empty
    have bound : 69≤Usize.max := by scalar_tac
    obtain ⟨out,after,run,source,rep,haddr,hcap,halloc,hhist,hframe⟩ :=
      PV_RDEAC_AfterCapacity.simulation ops step shape self digest "" e.buffer e.world repr
        (by rw [empty,cap];simp only [List.length_nil];omega) (by omega)
    refine ⟨out,after,?_,?_,?_,by omega,haddr,halloc,hhist,hframe⟩
    · unfold PV_RDEA_ReservationExecution.run
      change (match e.returned with | .error err => ((Except.error err : Except PV_RDB1_V183_ReserveWorld.Error (Buffer U8)),e.world) | .ok () => _) = _
      rw [h]
      exact run
    · simpa only [String.empty_append] using source
    · simpa only [String.empty_append] using rep

#print axioms simulation
end R1Z.PV_RDEAC_ConstructorSimulation
