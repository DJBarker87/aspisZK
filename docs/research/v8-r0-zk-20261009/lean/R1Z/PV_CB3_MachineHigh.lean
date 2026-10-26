import R1Z.PV_CB3_MachineDigits
import R1Z.PV_CB3_GammaBounds
import R1Z.PV_CB3_QuotientHead
namespace R1Z.PV_CB3_MachineHigh
open PV_CB3_SamplerWord PV_CB3_SamplerCarry
set_option autoImplicit false

def high (words : List (BitVec 32)) : BitVec 32 :=
  (PV_CB3_MachineDigits.split 8 words).2.headD 0

theorem headD_map (words : List (BitVec 32)) :
    (words.headD 0).toNat = (words.map BitVec.toNat).headD 0 := by
  cases words <;> rfl

theorem nat_headD (words : List Nat) (small : value radix words < radix) :
    value radix words = words.headD 0 := by
  cases words with
  | nil => rfl
  | cons w ws => exact PV_CB3_QuotientHead.head_value radix w ws small

theorem word_bounds (words : List (BitVec 32)) :
    ∀ w, w ∈ words.map BitVec.toNat → w < radix := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨d, _, rfl⟩
  exact d.isLt

/-- Reading word zero retains the complete quotient at this stage; every
higher word's contribution is zero by the previously proved rank bound. -/
theorem high_value (words : List (BitVec 32)) (length : words.length = 8) :
    (high words).toNat = value radix (words.map BitVec.toNat) / base ^ 8 := by
  have hp := (PV_CB3_MachineDigits.projection 8 words).2
  have hq := PV_CB3_DigitSequence.quotient_value base radix (by unfold base; omega) 8
    (words.map BitVec.toNat)
  have hs := PV_CB3_GammaBounds.high_small (words.map BitVec.toNat)
    (by simpa only [List.length_map] using length) (word_bounds words)
  have br : base < radix := by unfold base radix; omega
  have small : value radix ((PV_CB3_MachineDigits.split 8 words).2.map BitVec.toNat) < radix := by
    rw [hp, ← hq]
    omega
  dsimp only [high]
  rw [headD_map, ← nat_headD _ small, hp, ← hq]

theorem high_bound (words : List (BitVec 32)) (length : words.length = 8) :
    (high words).toNat < base := by
  rw [high_value words length]
  exact PV_CB3_GammaBounds.high_small (words.map BitVec.toNat)
    (by simpa only [List.length_map] using length) (word_bounds words)

#print axioms headD_map
#print axioms nat_headD
#print axioms word_bounds
#print axioms high_value
#print axioms high_bound
end R1Z.PV_CB3_MachineHigh
