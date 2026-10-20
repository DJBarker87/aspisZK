import AspisR1QueryGeometryActual.Funs
import R17TableAChunk02Certificate

set_option autoImplicit false

namespace R17NarrowFunsA02ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 64) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[0]!).2.val) = (400584953, 469433912) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨400584953, 469433912⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_00_zPow

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 65) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[1]!).2.val) = (469433912, 1746898694) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨469433912, 1746898694⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_01_zPow

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 66) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[2]!).2.val) = (932754395, 1184859162) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨932754395, 1184859162⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_02_zPow

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 67) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[3]!).2.val) = (1184859162, 1214729252) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1184859162, 1214729252⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_03_zPow

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 68) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[4]!).2.val) = (1636215277, 965201017) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1636215277, 965201017⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_04_zPow

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 69) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[5]!).2.val) = (965201017, 511268370) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨965201017, 511268370⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_05_zPow

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 70) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[6]!).2.val) = (993237774, 289789953) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨993237774, 289789953⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_06_zPow

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 71) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[7]!).2.val) = (289789953, 1154245873) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨289789953, 1154245873⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_07_zPow

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 72) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[8]!).2.val) = (1844375598, 1823771499) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1844375598, 1823771499⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_08_zPow

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 73) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[9]!).2.val) = (1823771499, 303108049) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1823771499, 303108049⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_09_zPow

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 74) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[10]!).2.val) = (1036868259, 1302232773) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1036868259, 1302232773⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_10_zPow

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 75) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[11]!).2.val) = (1302232773, 1110615388) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1302232773, 1110615388⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_11_zPow

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 76) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[12]!).2.val) = (1489475671, 1590331411) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1489475671, 1590331411⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_12_zPow

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 77) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[13]!).2.val) = (1590331411, 658007976) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1590331411, 658007976⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_13_zPow

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 78) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[14]!).2.val) = (271955858, 2011039234) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨271955858, 2011039234⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_14_zPow

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 79) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[15]!).2.val) = (2011039234, 1875527789) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2011039234, 1875527789⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_15_zPow

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 80) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[16]!).2.val) = (494932510, 292984488) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨494932510, 292984488⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_16_zPow

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 81) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[17]!).2.val) = (292984488, 1652551137) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨292984488, 1652551137⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_17_zPow

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 82) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[18]!).2.val) = (1415786230, 1111815158) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1415786230, 1111815158⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_18_zPow

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 83) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[19]!).2.val) = (1111815158, 731697417) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1111815158, 731697417⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_19_zPow

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 84) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[20]!).2.val) = (1150508049, 626837953) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1150508049, 626837953⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_20_zPow

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 85) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[21]!).2.val) = (626837953, 996975598) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨626837953, 996975598⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_21_zPow

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 86) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[22]!).2.val) = (317286896, 920117449) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨317286896, 920117449⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_22_zPow

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 87) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[23]!).2.val) = (920117449, 1830196751) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨920117449, 1830196751⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_23_zPow

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 88) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[24]!).2.val) = (1935941148, 1205027416) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1935941148, 1205027416⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_24_zPow

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 89) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[25]!).2.val) = (1205027416, 211542499) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1205027416, 211542499⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_25_zPow

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 90) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[26]!).2.val) = (809155383, 303944815) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨809155383, 303944815⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_26_zPow

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 91) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[27]!).2.val) = (303944815, 1338328264) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨303944815, 1338328264⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_27_zPow

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 92) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[28]!).2.val) = (541880188, 1280134915) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨541880188, 1280134915⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_28_zPow

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 93) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[29]!).2.val) = (1280134915, 1605603459) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1280134915, 1605603459⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_29_zPow

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 94) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[30]!).2.val) = (1598024857, 1875094528) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1598024857, 1875094528⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_30_zPow

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 95) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[31]!).2.val) = (1875094528, 549458790) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1875094528, 549458790⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk02Certificate.entry_31_zPow

#print axioms cell_31_circle_power

end R17NarrowFunsA02ChunkPower
