import R1Z.PV_CB3_MachineHigh
import R1Z.PV_CB3_MachineFinish
namespace R1Z.PV_CB3_MachineGamma
open PV_CB3_SamplerWord PV_CB3_SamplerCarry
set_option autoImplicit false

def gamma (words : List (BitVec 32)) : List (BitVec 32) :=
  PV_CB3_MachineFinish.finish (PV_CB3_MachineDigits.split 8 words).1
    (PV_CB3_MachineHigh.high words)

/-- Every actual machine digit in the typed pipeline equals its mathematical
recurrence digit. The sole shape premise is the source's eight-word input. -/
theorem projection (words : List (BitVec 32)) (length : words.length = 8) :
    (gamma words).map BitVec.toNat =
      PV_CB3_GammaRank.sampleDigits base radix 8 (words.map BitVec.toNat) := by
  dsimp only [gamma, PV_CB3_GammaRank.sampleDigits]
  rw [PV_CB3_MachineFinish.projection _ _ (PV_CB3_MachineHigh.high_bound words length),
    (PV_CB3_MachineDigits.projection 8 words).1,
    PV_CB3_MachineHigh.high_value words length,
    PV_CB3_DigitSequence.quotient_value base radix (by unfold base; omega)]

theorem length (words : List (BitVec 32)) (shape : words.length = 8) :
    (gamma words).length = 8 := by
  have h := congrArg List.length (projection words shape)
  simpa only [List.length_map, PV_CB3_GammaRank.sample_length] using h

theorem canonical (words : List (BitVec 32)) (shape : words.length = 8) :
    ∀ d, d ∈ gamma words → d.toNat < base := by
  intro d hd
  have hm : d.toNat ∈ (gamma words).map BitVec.toNat := List.mem_map.mpr ⟨d, hd, rfl⟩
  rw [projection words shape] at hm
  exact PV_CB3_GammaRank.sample_canonical base radix 8 (by unfold base; omega) _ _ hm

theorem value_formula (words : List (BitVec 32)) (shape : words.length = 8) :
    value base ((gamma words).map BitVec.toNat) =
      value radix (words.map BitVec.toNat) % (base ^ 8 - 1) + 1 := by
  rw [projection words shape]
  exact PV_CB3_GammaBounds.rank_formula _
    (by simpa only [List.length_map] using shape) (PV_CB3_MachineHigh.word_bounds words)

#print axioms projection
#print axioms length
#print axioms canonical
#print axioms value_formula
end R1Z.PV_CB3_MachineGamma
