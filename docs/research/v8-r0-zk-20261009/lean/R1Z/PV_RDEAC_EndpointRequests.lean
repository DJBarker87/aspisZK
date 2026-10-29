import R1Z.PV_RDEAC_EndpointFrames
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEAC_EndpointRequests
open PV_RDB1_V183_ReserveWorld PV_CBL_StringBytesAdapter PV_RDEAC_NameText

/-- Public request-size word for the actual owned-name consumer, including
constructor failure prefixes and cleanup. This is an auxiliary certificate;
returned values, addresses, errors, memory, frames and allocator state remain
in the full execution and are not replaced by this projection. -/
theorem prefix_word {S F : Type} (step : Request → S → Option Nat × S)
    (free : Nat → Nat → Nat → S → S) (shape : Shape) (width : shape.width=1)
    (nameAddress joinAddress : Nat) (digest : Array U8 32#usize) (base : List U8)
    (w : World S F) (owned : Buffer U8) (after : World S F)
    (run : PV_RDEA_ReservationExecution.run step shape nameAddress (digest.val.map PV_RDEAC_NibbleModel.byte) w=(.ok owned,after))
    (repr : owned.values=encodeList (basenameText digest.val)) :
    let e := PV_RDEAC_FullJoin.join step shape joinAddress false (PV_RDEAC_JoinValue.needsSeparator base) base owned.values after
    PV_RDEA_PrefixWords.Prefix (PV_RDEA_CapacityEndpoint.sizes (PV_RDEAC_JoinHandlers.finalWorld free owned e).history)
      ((PV_RDEA_CapacityEndpoint.sizes w.history++[(0,69,1)])++
        PV_RDEA_PathSchedule.joinWord base.length 69 false (PV_RDEAC_JoinValue.needsSeparator base)) := by
  dsimp only
  have len : (digest.val.map PV_RDEAC_NibbleModel.byte).length=32 := by rw [List.length_map];exact digest.property
  have stage := PV_RDEA_ReservationExecution.requests step shape width nameAddress _ len w
  rw [run] at stage
  have nameLen : owned.values.length=69 := by
    rw [repr,name_length]
    have hl : digest.val.length=32 := digest.property
    rw [hl]
  rw [(PV_RDEAC_JoinHandlers.frame_history free owned _).2]
  have h := PV_RDEA_JoinRequests.join_requests_prefix step shape width joinAddress false
    (PV_RDEAC_JoinValue.needsSeparator base) base owned.values after
  rw [←PV_RDEAC_FullJoin.projection] at h
  simp only [PV_RDEAC_JoinHandlers.erase_world] at h
  rw [stage,nameLen] at h
  exact h

theorem success_free {S F : Type} (free : Nat → Nat → Nat → S → S)
    (owned : Buffer U8) (e : Execution U8 S F) (cap : owned.capacity=69)
    (success : e.returned=.ok ()) :
    (PV_RDEAC_JoinHandlers.finalWorld free owned e).deallocCalls=e.world.deallocCalls+1 := by
  rw [PV_RDEAC_FreeWord.final_count]
  simp only [PV_RDEAC_FreeWord.word,success,PV_RDEAC_FreeWord.owned_word _ cap,List.length_cons,List.length_nil]

#print axioms prefix_word
#print axioms success_free
end R1Z.PV_RDEAC_EndpointRequests
