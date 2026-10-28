import R1Z.PV_RDEAC_CleanupHeaders
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEAC_PartialHeaders
open PV_RDB1_V183_ReserveWorld

theorem push_error {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (needSep : Bool) (b : Buffer U8) (path : List U8)
    (w : World S F) (err : PV_RDB1_V183_ReserveWorld.Error)
    (h : (PV_RDEAC_FullJoin.push step shape false needSep b path w).returned=.error err) :
    (PV_RDEAC_FullJoin.push step shape false needSep b path w).buffer.capacity=b.capacity ∨
    (PV_RDEAC_FullJoin.push step shape false needSep b path w).buffer.capacity=
      PV_RDEA_AppendRequests.nextCapacity b.values.length b.capacity 1 := by
  cases needSep with
  | false =>
    change (PV_RDEAC_FullAppend.append step shape b path w).returned=.error err at h
    exact Or.inl (congrArg (fun b : Buffer U8 => b.capacity) (PV_RDEAC_FullAppend.failed_header step shape b path w err h))
  | true =>
    change (PV_RDEAC_FullJoin.advance (PV_RDEAC_FullAppend.append step shape b [47#u8] w)
      (fun b w => PV_RDEAC_FullAppend.append step shape b path w)).returned=.error err at h
    change (PV_RDEAC_FullJoin.advance (PV_RDEAC_FullAppend.append step shape b [47#u8] w)
      (fun b w => PV_RDEAC_FullAppend.append step shape b path w)).buffer.capacity=_ ∨
      (PV_RDEAC_FullJoin.advance (PV_RDEAC_FullAppend.append step shape b [47#u8] w)
      (fun b w => PV_RDEAC_FullAppend.append step shape b path w)).buffer.capacity=_
    unfold PV_RDEAC_FullJoin.advance at h ⊢
    split at h <;> rename_i hs
    · exact Or.inl (congrArg (fun b : Buffer U8 => b.capacity) (PV_RDEAC_FullAppend.failed_header step shape b [47#u8] w _ hs))
    · rw [PV_RDEAC_FullAppend.failed_header step shape _ path _ err h]
      exact Or.inr (PV_RDEAC_CleanupHeaders.append_success step shape b [47#u8] w hs).1

theorem join_error {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (address : Nat) (needSep : Bool) (base path : List U8)
    (w : World S F) (err : PV_RDB1_V183_ReserveWorld.Error)
    (h : (PV_RDEAC_FullJoin.join step shape address false needSep base path w).returned=.error err) :
    (PV_RDEAC_FullJoin.join step shape address false needSep base path w).buffer.capacity=0 ∨
    (PV_RDEAC_FullJoin.join step shape address false needSep base path w).buffer.capacity=base.length ∨
    (PV_RDEAC_FullJoin.join step shape address false needSep base path w).buffer.capacity=
      PV_RDEA_AppendRequests.nextCapacity base.length base.length 1 := by
  unfold PV_RDEAC_FullJoin.join PV_RDEAC_FullJoin.advance at h ⊢
  split at h <;> rename_i hc
  · exact Or.inl (PV_RDEAC_FullClone.failed_capacity step shape address base w _ hc)
  · have head := PV_RDEAC_CleanupHeaders.clone_success step shape address base w hc
    have hp := push_error step shape needSep _ path _ err h
    rw [head.1,head.2] at hp
    exact Or.inr hp

#print axioms push_error
#print axioms join_error
end R1Z.PV_RDEAC_PartialHeaders
