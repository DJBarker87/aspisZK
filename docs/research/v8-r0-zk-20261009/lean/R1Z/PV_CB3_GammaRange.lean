import R1Z.PV_CB3_StagedGammaRank
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_GammaRange
open Aeneas Aeneas.Std
open PV_CB3_StagedGammaRank

theorem modulus_positive : 0 < PV_CB3_SamplerWord.base^8-1 := by
  have hb : 1 < PV_CB3_SamplerWord.base := by unfold PV_CB3_SamplerWord.base; omega
  have hp : PV_CB3_SamplerWord.base^1 ≤ PV_CB3_SamplerWord.base^8 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  simp only [Nat.pow_one] at hp
  omega

theorem positive (block : Array U8 32#usize) : 0 < outputRank (result block) := by
  rw [rank]
  omega

theorem bounded (block : Array U8 32#usize) :
    outputRank (result block) ≤ PV_CB3_SamplerWord.base^8-1 := by
  rw [rank]
  have hm := Nat.mod_lt (byteRank block) modulus_positive
  omega

theorem byte_bound (block : Array U8 32#usize) : byteRank block < 256^32 := by
  have h := PV_CB3_SamplerCarry.value_lt_pow 256 (block.val.map UScalar.val) (by
    intro d hd
    rcases List.mem_map.mp hd with ⟨x,hx,rfl⟩
    exact PV_CB3_StagedLoadInspect.byte_bound x)
  simpa [byteRank,List.length_map,block.property] using h
#print axioms modulus_positive
#print axioms positive
#print axioms bounded
#print axioms byte_bound
end R1Z.PV_CB3_GammaRange
