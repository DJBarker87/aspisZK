import R1Z.PV_RDEAC_FullJoin
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEAC_CapacityBounds
open PV_RDB1_V183_ReserveWorld

theorem constructor {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address n : Nat) (w : World S F)
    (h : (PV_RDB1_V181.deployed step 18446744073709551615 9223372036854775807 shape address n w).returned=.ok ()) :
    (PV_RDB1_V181.deployed step 18446744073709551615 9223372036854775807 shape address n w).buffer.capacity≤9223372036854775807 := by
  rw [PV_RDEA_CloneExecution.capacity_success step shape address n w h]
  unfold PV_RDB1_V181.deployed at h
  split at h <;> rename_i hn
  · cases h
  · split at h <;> rename_i hb
    · cases h
    · rw [width] at hb
      omega

theorem reserve {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (b : Buffer U8)
    (tail : List U8) (w : World S F) (initial : b.capacity≤9223372036854775807)
    (h : (PV_RDB1_Append.reserve step 18446744073709551615 9223372036854775807 shape b tail.length w).returned=.ok ()) :
    (PV_RDB1_Append.reserve step 18446744073709551615 9223372036854775807 shape b tail.length w).buffer.capacity≤9223372036854775807 := by
  unfold PV_RDB1_Append.reserve at h ⊢
  split at h <;> rename_i enough
  · simp only [enough,if_true];exact initial
  · simp only [enough,if_false]
    split at h <;> rename_i word
    · cases h
    · simp only [word,if_false]
      split at h <;> rename_i bytes
      · cases h
      · simp only [bytes,if_false]
        unfold PV_RDB1_Append.finishAt
        dsimp only
        cases hs : step ⟨b.address,b.capacity,PV_RDB1_Append.growthCapacity b.values.length b.capacity tail.length,shape⟩ w.allocator with
        | mk p s => cases p <;> simp only [hs]
                    · exact initial
                    · rw [width] at bytes;omega

#print axioms constructor
#print axioms reserve
end R1Z.PV_RDEAC_CapacityBounds
