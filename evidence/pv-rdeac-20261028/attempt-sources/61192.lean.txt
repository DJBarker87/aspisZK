import R1Z.PV_RDEAC_EndpointInstance
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEAC_LiteralDomain
open PV_RDB1_V183_ReserveWorld

theorem no_overflow {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat) (w : World S F) :
    (PV_RDB1_V181.deployed step 18446744073709551615 9223372036854775807 shape address 69 w).returned≠.error .capacityOverflow := by
  rw [show 69=PV_RDEA_V181.reservationCapacity from rfl,
    PV_RDEA_V181.reachable_constructor step shape width]
  unfold finish
  dsimp only
  cases hs : step ⟨address,0,69,shape⟩ w.allocator with
  | mk p s => cases p <;> simp [PV_RDB1_V181.empty,PV_RDEA_V181.reservationCapacity,hs]

theorem error_kind {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat) (w : World S F)
    (err : PV_RDB1_V183_ReserveWorld.Error)
    (h : (PV_RDB1_V181.deployed step 18446744073709551615 9223372036854775807 shape address 69 w).returned=.error err) :
    ∃ layout,err=.allocError layout := by
  cases err with
  | capacityOverflow => exact False.elim (no_overflow step shape width address w h)
  | allocError layout => exact ⟨layout,rfl⟩

#print axioms no_overflow
#print axioms error_kind
end R1Z.PV_RDEAC_LiteralDomain
