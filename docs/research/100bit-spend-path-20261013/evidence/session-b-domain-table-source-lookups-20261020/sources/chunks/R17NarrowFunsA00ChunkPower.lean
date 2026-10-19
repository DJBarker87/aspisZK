import AspisR1QueryGeometryActual.Funs
import R17TableAChunk00Certificate

set_option autoImplicit false

namespace R17NarrowFunsA00ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 0) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[0]!).2.val) = (1022251061, 788094511) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1022251061, 788094511⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_00]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 1) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[1]!).2.val) = (788094511, 1125232586) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨788094511, 1125232586⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_01]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 2) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[2]!).2.val) = (1462922215, 117240331) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1462922215, 117240331⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_02]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 3) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[3]!).2.val) = (117240331, 684561432) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨117240331, 684561432⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_03]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 4) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[4]!).2.val) = (479936188, 217587789) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨479936188, 217587789⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_04]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 5) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[5]!).2.val) = (217587789, 1667547459) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨217587789, 1667547459⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_05]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 6) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[6]!).2.val) = (797223315, 1892184156) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨797223315, 1892184156⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_06]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 7) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[7]!).2.val) = (1892184156, 1350260332) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1892184156, 1350260332⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_07]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 8) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[8]!).2.val) = (1601663285, 2022005567) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1601663285, 2022005567⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_08]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 9) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[9]!).2.val) = (2022005567, 545820362) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2022005567, 545820362⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_09]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 10) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[10]!).2.val) = (1715132412, 1963268365) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1715132412, 1963268365⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_10]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 11) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[11]!).2.val) = (1963268365, 432351235) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1963268365, 432351235⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_11]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 12) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[12]!).2.val) = (1329069890, 1640136239) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1329069890, 1640136239⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_12]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 13) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[13]!).2.val) = (1640136239, 818413757) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1640136239, 818413757⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_13]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 14) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[14]!).2.val) = (1052324090, 1064735370) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1052324090, 1064735370⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_14]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 15) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[15]!).2.val) = (1064735370, 1095159557) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1064735370, 1095159557⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_15]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 16) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[16]!).2.val) = (119109612, 1742172267) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨119109612, 1742172267⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_16]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 17) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[17]!).2.val) = (1742172267, 2028374035) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1742172267, 2028374035⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_17]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 18) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[18]!).2.val) = (1949036272, 2084561085) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1949036272, 2084561085⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_18]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 19) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[19]!).2.val) = (2084561085, 198447375) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2084561085, 198447375⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_19]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 20) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[20]!).2.val) = (1276985988, 456990464) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1276985988, 456990464⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_20]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 21) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[21]!).2.val) = (456990464, 870497659) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨456990464, 870497659⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_21]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 22) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[22]!).2.val) = (818046810, 1849544479) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨818046810, 1849544479⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_22]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 23) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[23]!).2.val) = (1849544479, 1329436837) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1849544479, 1329436837⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_23]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 24) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[24]!).2.val) = (1068288753, 675427495) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1068288753, 675427495⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_24]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 25) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[25]!).2.val) = (675427495, 1079194894) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨675427495, 1079194894⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_25]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 26) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[26]!).2.val) = (2144102382, 886761621) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2144102382, 886761621⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_26]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 27) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[27]!).2.val) = (886761621, 3381265) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨886761621, 3381265⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_27]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 28) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[28]!).2.val) = (1542630618, 1177056098) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1542630618, 1177056098⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_28]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 29) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[29]!).2.val) = (1177056098, 604853029) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1177056098, 604853029⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_29]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 30) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[30]!).2.val) = (270443035, 1665395253) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨270443035, 1665395253⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_30]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 31) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[31]!).2.val) = (1665395253, 1877040612) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1665395253, 1877040612⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk00Certificate.entry_31]
  exact R17TableAChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsA00ChunkPower
