import R1Z.PV_CB3_MachineCarryStep
import R1Z.PV_CB3_SamplerCarry
namespace R1Z.PV_CB3_MachineCarry
open PV_CB3_SamplerWord
set_option autoImplicit false

def carry : List (BitVec 32) → BitVec 32 → List (BitVec 32) × BitVec 32
  | [], addend => ([], addend)
  | d :: ds, addend =>
    let head := PV_CB3_MachineCarryStep.step d addend
    let tail := carry ds head.2
    (head.1 :: tail.1, tail.2)

theorem length_preserved (digits : List (BitVec 32)) (addend : BitVec 32) :
    (carry digits addend).1.length = digits.length := by
  induction digits generalizing addend with
  | nil => rfl
  | cons d ds ih => simp only [carry, List.length_cons, ih]

/-- Exact full-vector carry transport for arbitrary words and addend.
No precondition constrains the answer or the input digit range. -/
theorem projection (digits : List (BitVec 32)) (addend : BitVec 32) :
    (carry digits addend).1.map BitVec.toNat =
      (PV_CB3_SamplerCarry.addCarry base (digits.map BitVec.toNat) addend.toNat).1 ∧
    (carry digits addend).2.toNat =
      (PV_CB3_SamplerCarry.addCarry base (digits.map BitVec.toNat) addend.toNat).2 := by
  induction digits generalizing addend with
  | nil => exact ⟨rfl, rfl⟩
  | cons d ds ih =>
    have hs := PV_CB3_MachineCarryStep.projection d addend
    have ht := ih (PV_CB3_MachineCarryStep.step d addend).2
    dsimp only [carry, PV_CB3_SamplerCarry.addCarry]
    simp only [List.map_cons, PV_CB3_SamplerCarry.addCarry]
    rw [ht.1, ht.2, hs.1, hs.2]
    exact ⟨rfl, rfl⟩

theorem canonical (digits : List (BitVec 32)) (addend : BitVec 32) :
    ∀ d, d ∈ (carry digits addend).1 → d.toNat < base := by
  intro d hd
  have hm : d.toNat ∈ (carry digits addend).1.map BitVec.toNat := List.mem_map.mpr ⟨d, hd, rfl⟩
  rw [(projection digits addend).1] at hm
  exact PV_CB3_SamplerCarry.digits_canonical base (by unfold base; omega) _ _ _ hm

#print axioms length_preserved
#print axioms projection
#print axioms canonical
end R1Z.PV_CB3_MachineCarry
