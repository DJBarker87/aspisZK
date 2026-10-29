import R1Z.PV_RDEAC_SourceTail
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEAC_EndpointFrames
open PV_RDB1_V183_ReserveWorld

theorem name_frame {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat)
    (digest : Array U8 32#usize) (w : World S F) :
    (PV_RDEA_ReservationExecution.run step shape address (digest.val.map PV_RDEAC_NibbleModel.byte) w).2.frame=w.frame := by
  let e := PV_RDB1_V181.deployed step 18446744073709551615 9223372036854775807 shape address 69 w
  have frame : e.world.frame=w.frame := PV_RDEAC_Frames.constructor step shape address 69 w
  unfold PV_RDEA_ReservationExecution.run
  change (match e.returned with
    | .error err => ((Except.error err : Except PV_RDB1_V183_ReserveWorld.Error (Buffer U8)),e.world)
    | .ok () => PV_RDEA_NameFill.fill step shape (digest.val.map PV_RDEAC_NibbleModel.byte) e.buffer e.world).2.frame=w.frame
  cases h : e.returned with
  | error err => exact frame
  | ok unit =>
    have cap : e.buffer.capacity=69 := PV_RDEA_CloneExecution.capacity_success step shape address 69 w h
    have empty : e.buffer.values=[] := PV_RDB1_V181.empty_value step _ _ shape width address 69 w
    have len : digest.val.length=32 := digest.property
    have fits : e.buffer.values.length+2*(digest.val.map PV_RDEAC_NibbleModel.byte).length+5≤e.buffer.capacity := by
      rw [empty,cap,List.length_map,len]
      simp only [List.length_nil]
      omega
    obtain ⟨out,after,run,_,_,_,_,_,hf⟩ := PV_RDEA_NameFill.complete step shape _ e.buffer e.world fits
    rw [run]
    exact hf.trans frame

theorem final_frame {S F : Type} (step : Request → S → Option Nat × S)
    (free : Nat → Nat → Nat → S → S) (shape : Shape) (width : shape.width=1)
    (nameAddress joinAddress : Nat) (digest : Array U8 32#usize)
    (base : List U8) (needSep : Bool) (w : World S F) (owned : Buffer U8) (after : World S F)
    (run : PV_RDEA_ReservationExecution.run step shape nameAddress (digest.val.map PV_RDEAC_NibbleModel.byte) w=(.ok owned,after)) :
    (PV_RDEAC_JoinHandlers.finalWorld free owned
      (PV_RDEAC_FullJoin.join step shape joinAddress false needSep base owned.values after)).frame=w.frame := by
  have frame := name_frame step shape width nameAddress digest w
  rw [run] at frame
  exact (PV_RDEAC_JoinHandlers.frame_history free owned _).1.trans
    ((PV_RDEAC_Frames.join step shape joinAddress false needSep base owned.values after).trans frame)

#print axioms name_frame
#print axioms final_frame
end R1Z.PV_RDEAC_EndpointFrames
