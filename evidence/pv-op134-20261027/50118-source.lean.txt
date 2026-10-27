import R1Z.PV_Op134_MaskBits0
import R1Z.PV_Op134_MaskBits1
import R1Z.PV_Op134_MaskBits2
import R1Z.PV_Op134_MaskBits3
import R1Z.PV_Op134_MaskBits4
import R1Z.PV_Op134_MaskBits5
import R1Z.PV_Op134_MaskBits6
import R1Z.PV_Op134_MaskBits7
import R1Z.PV_Op134_RowOrder
namespace R1Z.PV_Op134_MaskSpec
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem bits (block : Fin 64) (bit : Fin 16) :
    Nat.testBit (PV_Op134_Masks.masks.val[block.val]'(by
      rw [PV_Op134_Masks.length]; exact block.isLt)).val bit.val = true ↔
      16*block.val+bit.val ∈ PV_Op134_RowSpec.rows.map (fun r => r.val) := by
  have hb := block.isLt
  by_cases h0 : block.val < 8
  · let j : Fin 8 := ⟨block.val-0,by omega⟩
    have he : 0+j.val=block.val := by dsimp [j]; omega
    simpa only [he] using PV_Op134_MaskBits0.bits j bit
  ·
    by_cases h1 : block.val < 16
    · let j : Fin 8 := ⟨block.val-8,by omega⟩
      have he : 8+j.val=block.val := by dsimp [j]; omega
      simpa only [he] using PV_Op134_MaskBits1.bits j bit
    ·
      by_cases h2 : block.val < 24
      · let j : Fin 8 := ⟨block.val-16,by omega⟩
        have he : 16+j.val=block.val := by dsimp [j]; omega
        simpa only [he] using PV_Op134_MaskBits2.bits j bit
      ·
        by_cases h3 : block.val < 32
        · let j : Fin 8 := ⟨block.val-24,by omega⟩
          have he : 24+j.val=block.val := by dsimp [j]; omega
          simpa only [he] using PV_Op134_MaskBits3.bits j bit
        ·
          by_cases h4 : block.val < 40
          · let j : Fin 8 := ⟨block.val-32,by omega⟩
            have he : 32+j.val=block.val := by dsimp [j]; omega
            simpa only [he] using PV_Op134_MaskBits4.bits j bit
          ·
            by_cases h5 : block.val < 48
            · let j : Fin 8 := ⟨block.val-40,by omega⟩
              have he : 40+j.val=block.val := by dsimp [j]; omega
              simpa only [he] using PV_Op134_MaskBits5.bits j bit
            ·
              by_cases h6 : block.val < 56
              · let j : Fin 8 := ⟨block.val-48,by omega⟩
                have he : 48+j.val=block.val := by dsimp [j]; omega
                simpa only [he] using PV_Op134_MaskBits6.bits j bit
              ·
                let j : Fin 8 := ⟨block.val-56,by omega⟩
                have he : 56+j.val=block.val := by dsimp [j]; omega
                simpa only [he] using PV_Op134_MaskBits7.bits j bit

#print axioms bits
end R1Z.PV_Op134_MaskSpec
