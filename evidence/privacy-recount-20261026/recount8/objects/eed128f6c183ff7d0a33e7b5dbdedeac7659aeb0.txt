import R1Z.PV_RDEAC_CapacityBounds
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEAC_FullCaps
open PV_RDB1_V183_ReserveWorld

def Capped {S F : Type} (e : Execution U8 S F) : Prop :=
  e.returned=.ok () → e.buffer.capacity≤9223372036854775807

theorem append_capacity {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (b : Buffer U8) (tail : List U8) (w : World S F) :
    (PV_RDEAC_FullAppend.append step shape b tail w).buffer.capacity=
      (PV_RDB1_Append.reserve step 18446744073709551615 9223372036854775807 shape b tail.length w).buffer.capacity := by
  unfold PV_RDEAC_FullAppend.append
  dsimp only
  split <;> rfl

theorem append_returned {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (b : Buffer U8) (tail : List U8) (w : World S F) :
    (PV_RDEAC_FullAppend.append step shape b tail w).returned=
      (PV_RDB1_Append.reserve step 18446744073709551615 9223372036854775807 shape b tail.length w).returned := by
  unfold PV_RDEAC_FullAppend.append
  dsimp only
  split <;> rename_i h
  · rfl
  · exact h.symm

theorem append {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (b : Buffer U8) (tail : List U8)
    (w : World S F) (initial : b.capacity≤9223372036854775807) :
    Capped (PV_RDEAC_FullAppend.append step shape b tail w) := by
  intro h
  rw [append_returned] at h
  rw [append_capacity]
  exact PV_RDEAC_CapacityBounds.reserve step shape width b tail w initial h

theorem clone {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat) (base : List U8) (w : World S F) :
    Capped (PV_RDEAC_FullClone.clone step shape address base w) := by
  intro h
  unfold PV_RDEAC_FullClone.clone at h ⊢
  dsimp only at h ⊢
  split at h <;> rename_i hr
  · rw [hr] at h
    cases h
  · exact PV_RDEAC_CapacityBounds.constructor step shape width address base.length w hr

theorem advance {S F : Type} (e : Execution U8 S F)
    (next : Buffer U8 → World S F → Execution U8 S F) (first : Capped e)
    (more : ∀ b w, b.capacity≤9223372036854775807 → Capped (next b w)) :
    Capped (PV_RDEAC_FullJoin.advance e next) := by
  cases e with
  | mk returned b w =>
    cases returned with
    | error err => intro h;cases h
    | ok unit => exact more b w (first rfl)

theorem join {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat) (absolute needSep : Bool)
    (base path : List U8) (w : World S F) :
    Capped (PV_RDEAC_FullJoin.join step shape address absolute needSep base path w) := by
  unfold PV_RDEAC_FullJoin.join
  apply advance _ _ (clone step shape width address base w)
  intro b w initial
  unfold PV_RDEAC_FullJoin.push
  apply advance
  · cases absolute <;> intro _ <;> exact initial
  · intro b w initial
    apply advance
    · split
      · exact append step shape width b [47#u8] w initial
      · intro _;exact initial
    · intro b w initial
      exact append step shape width b path w initial

#print axioms append_capacity
#print axioms append_returned
#print axioms append
#print axioms clone
#print axioms advance
#print axioms join
end R1Z.PV_RDEAC_FullCaps
