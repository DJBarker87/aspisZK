import AspisR1QueryGeometryActual.Funs
import R17TableBChunk09Certificate

set_option autoImplicit false

namespace R17NarrowFunsB09ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 288) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[0]!).2.val) = (1421883301, 1767600112) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1421883301, 1767600112⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_00]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 289) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[1]!).2.val) = (1742158212, 947474543) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1742158212, 947474543⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_01]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 290) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[2]!).2.val) = (848823435, 1634673682) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨848823435, 1634673682⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_02]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 291) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[3]!).2.val) = (47282233, 1973840192) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨47282233, 1973840192⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_03]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 292) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[4]!).2.val) = (1318914216, 1663922738) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1318914216, 1663922738⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_04]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 293) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[5]!).2.val) = (500001204, 1350892375) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨500001204, 1350892375⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_05]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 294) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[6]!).2.val) = (2079323762, 1208852267) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2079323762, 1208852267⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_06]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 295) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[7]!).2.val) = (1386607805, 2069854787) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1386607805, 2069854787⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_07]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 296) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[8]!).2.val) = (729011542, 952009042) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨729011542, 952009042⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_08]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 297) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[9]!).2.val) = (1995718635, 990602029) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1995718635, 990602029⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_09]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 298) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[10]!).2.val) = (1079208008, 2008108071) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1079208008, 2008108071⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_10]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 299) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[11]!).2.val) = (985150678, 1044660427) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨985150678, 1044660427⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_11]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 300) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[12]!).2.val) = (782570832, 476532960) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨782570832, 476532960⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_12]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 301) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[13]!).2.val) = (649844810, 475157379) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨649844810, 475157379⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_13]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 302) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[14]!).2.val) = (1462196868, 1013065725) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1462196868, 1013065725⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_14]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 303) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[15]!).2.val) = (405825245, 2000126861) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨405825245, 2000126861⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_15]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 304) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[16]!).2.val) = (606906923, 1264738384) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨606906923, 1264738384⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_16]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 305) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[17]!).2.val) = (875583808, 1932435950) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨875583808, 1932435950⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_17]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 306) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[18]!).2.val) = (1771477961, 772209956) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1771477961, 772209956⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_18]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 307) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[19]!).2.val) = (1153435498, 735309441) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1153435498, 735309441⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_19]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 308) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[20]!).2.val) = (291679777, 1578449442) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨291679777, 1578449442⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_20]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 309) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[21]!).2.val) = (1036739736, 4090232) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1036739736, 4090232⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_21]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 310) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[22]!).2.val) = (1954195642, 800757595) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1954195642, 800757595⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_22]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 311) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[23]!).2.val) = (3045475, 162418948) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨3045475, 162418948⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_23]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 312) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[24]!).2.val) = (953139263, 265503960) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨953139263, 265503960⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_24]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 313) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[25]!).2.val) = (1255153497, 1873206092) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1255153497, 1873206092⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_25]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 314) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[26]!).2.val) = (1109468214, 24685739) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1109468214, 24685739⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_26]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 315) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[27]!).2.val) = (1194288306, 1664016260) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1194288306, 1664016260⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_27]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 316) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[28]!).2.val) = (1954241062, 1820169310) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1954241062, 1820169310⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_28]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 317) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[29]!).2.val) = (461636029, 555407991) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨461636029, 555407991⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_29]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 318) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[30]!).2.val) = (878071934, 497955134) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨878071934, 497955134⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_30]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 319) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[31]!).2.val) = (1274127696, 398642911) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1274127696, 398642911⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk09Certificate.entry_31]
  exact R17TableBChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB09ChunkPower
