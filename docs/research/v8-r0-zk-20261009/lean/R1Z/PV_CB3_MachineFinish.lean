import R1Z.PV_CB3_MachineCarry
import R1Z.PV_CB3_GammaDigits
namespace R1Z.PV_CB3_MachineFinish
open PV_CB3_SamplerWord PV_CB3_MachineCarry
set_option autoImplicit false

def finish (digits : List (BitVec 32)) (high : BitVec 32) : List (BitVec 32) :=
  let first := carry digits (high + 1)
  if first.2 = 0 then first.1 else (carry first.1 1).1

theorem increment_value (high : BitVec 32) (bound : high.toNat < base) :
    (high + 1).toNat = high.toNat + 1 := by
  rw [BitVec.toNat_add]
  change (high.toNat + 1) % 4294967296 = high.toNat + 1
  apply Nat.mod_eq_of_lt
  unfold base at bound
  omega

/-- The machine's actual overflow-word test selects exactly the mathematical
wrap branch; the high-word range is an internal division invariant. -/
theorem projection (digits : List (BitVec 32)) (high : BitVec 32)
    (bound : high.toNat < base) :
    (finish digits high).map BitVec.toNat =
      PV_CB3_GammaDigits.finish base (digits.map BitVec.toNat) high.toNat := by
  have hp := PV_CB3_MachineCarry.projection digits (high + 1)
  rw [increment_value high bound] at hp
  have hz : (carry digits (high + 1)).2 = 0 ↔
      (PV_CB3_SamplerCarry.addCarry base (digits.map BitVec.toNat) (high.toNat + 1)).2 = 0 := by
    rw [← hp.2]
    constructor
    · intro h; rw [h]; rfl
    · intro h; apply BitVec.eq_of_toNat_eq; simpa using h
  dsimp only [finish, PV_CB3_GammaDigits.finish]
  by_cases h : (carry digits (high + 1)).2 = 0
  · rw [if_pos h, if_pos (hz.mp h), hp.1]
  · rw [if_neg h, if_neg (fun z => h (hz.mpr z)),
      (PV_CB3_MachineCarry.projection (carry digits (high + 1)).1 1).1, hp.1]
    rfl

#print axioms increment_value
#print axioms projection
end R1Z.PV_CB3_MachineFinish
