import AspisR1QueryGeometryActual.Funs
import R17TableAChunk07Certificate

set_option autoImplicit false

namespace R17NarrowFunsA07ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 224) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[0]!).2.val) = (188438465, 212575099) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨188438465, 212575099⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_00]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 225) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[1]!).2.val) = (212575099, 1959045182) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨212575099, 1959045182⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_01]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 226) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[2]!).2.val) = (2107512806, 635240816) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2107512806, 635240816⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_02]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 227) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[3]!).2.val) = (635240816, 39970841) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨635240816, 39970841⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_03]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 228) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[4]!).2.val) = (1351399750, 1217896196) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1351399750, 1217896196⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_04]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 229) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[5]!).2.val) = (1217896196, 796083897) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1217896196, 796083897⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_05]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 230) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[6]!).2.val) = (740661540, 1927215114) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨740661540, 1927215114⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_06]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 231) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[7]!).2.val) = (1927215114, 1406822107) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1927215114, 1406822107⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_07]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 232) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[8]!).2.val) = (558100220, 1980501108) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨558100220, 1980501108⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_08]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 233) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[9]!).2.val) = (1980501108, 1589383427) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1980501108, 1589383427⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_09]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 234) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[10]!).2.val) = (2109249359, 247223496) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2109249359, 247223496⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_10]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 235) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[11]!).2.val) = (247223496, 38234288) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨247223496, 38234288⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_11]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 236) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[12]!).2.val) = (1012525923, 71691935) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1012525923, 71691935⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_12]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 237) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[13]!).2.val) = (71691935, 1134957724) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨71691935, 1134957724⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_13]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 238) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[14]!).2.val) = (1828798623, 27117548) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1828798623, 27117548⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_14]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 239) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[15]!).2.val) = (27117548, 318685024) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨27117548, 318685024⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_15]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 240) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[16]!).2.val) = (2039959946, 1457037680) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2039959946, 1457037680⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_16]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 241) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[17]!).2.val) = (1457037680, 107523701) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1457037680, 107523701⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_17]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 242) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[18]!).2.val) = (2038288495, 670227777) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2038288495, 670227777⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_18]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 243) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[19]!).2.val) = (670227777, 109195152) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨670227777, 109195152⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_19]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 244) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[20]!).2.val) = (209663158, 168116384) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨209663158, 168116384⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_20]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 245) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[21]!).2.val) = (168116384, 1937820489) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨168116384, 1937820489⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_21]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 246) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[22]!).2.val) = (984290948, 99941766) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨984290948, 99941766⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_22]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 247) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[23]!).2.val) = (99941766, 1163192699) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨99941766, 1163192699⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_23]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 248) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[24]!).2.val) = (1252927563, 799345076) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1252927563, 799345076⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_24]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 249) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[25]!).2.val) = (799345076, 894556084) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨799345076, 894556084⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_25]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 250) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[26]!).2.val) = (419428947, 1890870518) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨419428947, 1890870518⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_26]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 251) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[27]!).2.val) = (1890870518, 1728054700) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1890870518, 1728054700⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_27]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 252) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[28]!).2.val) = (1157494553, 1817015079) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1157494553, 1817015079⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_28]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 253) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[29]!).2.val) = (1817015079, 989989094) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1817015079, 989989094⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_29]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 254) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[30]!).2.val) = (891334987, 1040656207) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨891334987, 1040656207⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_30]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 255) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[31]!).2.val) = (1040656207, 1256148660) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1040656207, 1256148660⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk07Certificate.entry_31]
  exact R17TableAChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsA07ChunkPower
