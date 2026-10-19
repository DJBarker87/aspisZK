import AspisR1QueryGeometryActual.Funs
import R17TableAChunk10Certificate

set_option autoImplicit false

namespace R17NarrowFunsA10ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 320) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[0]!).2.val) = (894752084, 1749876144) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨894752084, 1749876144⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_00]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 321) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[1]!).2.val) = (1749876144, 1252731563) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1749876144, 1252731563⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_01]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 322) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[2]!).2.val) = (1770167713, 338572024) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1770167713, 338572024⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_02]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 323) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[3]!).2.val) = (338572024, 377315934) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨338572024, 377315934⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_03]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 324) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[4]!).2.val) = (1674153723, 1322319557) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1674153723, 1322319557⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_04]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 325) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[5]!).2.val) = (1322319557, 473329924) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1322319557, 473329924⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_05]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 326) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[6]!).2.val) = (1189130906, 937749255) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1189130906, 937749255⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_06]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 327) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[7]!).2.val) = (937749255, 958352741) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨937749255, 958352741⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_07]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 328) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[8]!).2.val) = (406765125, 1121751370) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨406765125, 1121751370⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_08]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 329) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[9]!).2.val) = (1121751370, 1740718522) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1121751370, 1740718522⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_09]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 330) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[10]!).2.val) = (667409179, 1770171037) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨667409179, 1770171037⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_10]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 331) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[11]!).2.val) = (1770171037, 1480074468) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1770171037, 1480074468⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_11]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 332) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[12]!).2.val) = (336549856, 2103544920) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨336549856, 2103544920⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_12]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 333) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[13]!).2.val) = (2103544920, 1810933791) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2103544920, 1810933791⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_13]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 334) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[14]!).2.val) = (1914474864, 440166738) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1914474864, 440166738⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_14]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 335) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[15]!).2.val) = (440166738, 233008783) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨440166738, 233008783⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_15]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 336) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[16]!).2.val) = (2003660710, 1164690642) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2003660710, 1164690642⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_16]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 337) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[17]!).2.val) = (1164690642, 143822937) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1164690642, 143822937⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_17]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 338) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[18]!).2.val) = (440188121, 714460670) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨440188121, 714460670⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_18]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 339) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[19]!).2.val) = (714460670, 1707295526) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨714460670, 1707295526⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_19]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 340) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[20]!).2.val) = (1894212231, 1899640059) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1894212231, 1899640059⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_20]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 341) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[21]!).2.val) = (1899640059, 253271416) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1899640059, 253271416⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_21]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 342) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[22]!).2.val) = (1270997537, 1765408850) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1270997537, 1765408850⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_22]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 343) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[23]!).2.val) = (1765408850, 876486110) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1765408850, 876486110⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_23]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 344) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[24]!).2.val) = (834173210, 2010056637) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨834173210, 2010056637⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_24]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 345) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[25]!).2.val) = (2010056637, 1313310437) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2010056637, 1313310437⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_25]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 346) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[26]!).2.val) = (1080830343, 1196541462) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1080830343, 1196541462⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_26]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 347) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[27]!).2.val) = (1196541462, 1066653304) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1196541462, 1066653304⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_27]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 348) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[28]!).2.val) = (703912353, 1783773358) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨703912353, 1783773358⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_28]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 349) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[29]!).2.val) = (1783773358, 1443571294) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1783773358, 1443571294⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_29]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 350) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[30]!).2.val) = (153621575, 797360221) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨153621575, 797360221⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_30]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 351) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[31]!).2.val) = (797360221, 1993862072) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨797360221, 1993862072⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk10Certificate.entry_31]
  exact R17TableAChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsA10ChunkPower
