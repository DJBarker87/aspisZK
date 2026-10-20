import AspisR1QueryGeometryActual.Funs
import R17TableAChunk09Certificate

set_option autoImplicit false

namespace R17NarrowFunsA09ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 288) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[0]!).2.val) = (381944357, 1303428041) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨381944357, 1303428041⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_00]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 289) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[1]!).2.val) = (1303428041, 1765539290) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1303428041, 1765539290⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_01]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 290) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[2]!).2.val) = (1593271412, 1557280492) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1593271412, 1557280492⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_02]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 291) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[3]!).2.val) = (1557280492, 554212235) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1557280492, 554212235⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_03]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 292) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[4]!).2.val) = (2095613886, 527857063) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2095613886, 527857063⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_04]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 293) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[5]!).2.val) = (527857063, 51869761) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨527857063, 51869761⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_05]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 294) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[6]!).2.val) = (2125667422, 1995711117) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2125667422, 1995711117⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_06]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 295) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[7]!).2.val) = (1995711117, 21816225) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1995711117, 21816225⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_07]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 296) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[8]!).2.val) = (1589276025, 1583924546) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1589276025, 1583924546⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_08]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 297) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[9]!).2.val) = (1583924546, 558207622) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1583924546, 558207622⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_09]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 298) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[10]!).2.val) = (425606435, 736395182) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨425606435, 736395182⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_10]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 299) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[11]!).2.val) = (736395182, 1721877212) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨736395182, 1721877212⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_11]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 300) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[12]!).2.val) = (820025422, 857904003) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨820025422, 857904003⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_12]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 301) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[13]!).2.val) = (857904003, 1327458225) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨857904003, 1327458225⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_13]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 302) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[14]!).2.val) = (367584259, 2107277889) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨367584259, 2107277889⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_14]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 303) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[15]!).2.val) = (2107277889, 1779899388) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2107277889, 1779899388⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_15]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 304) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[16]!).2.val) = (1845204024, 116979180) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1845204024, 116979180⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_16]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 305) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[17]!).2.val) = (116979180, 302279623) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨116979180, 302279623⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_17]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 306) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[18]!).2.val) = (1158837492, 819566845) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1158837492, 819566845⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_18]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 307) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[19]!).2.val) = (819566845, 988646155) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨819566845, 988646155⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_19]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 308) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[20]!).2.val) = (1766982315, 596409291) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1766982315, 596409291⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_20]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 309) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[21]!).2.val) = (596409291, 380501332) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨596409291, 380501332⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_21]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 310) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[22]!).2.val) = (1060867294, 1016052282) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1060867294, 1016052282⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_22]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 311) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[23]!).2.val) = (1016052282, 1086616353) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1016052282, 1086616353⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_23]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 312) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[24]!).2.val) = (15470579, 1643565293) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨15470579, 1643565293⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_24]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 313) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[25]!).2.val) = (1643565293, 2132013068) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1643565293, 2132013068⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_25]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 314) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[26]!).2.val) = (1886413538, 1618829578) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1886413538, 1618829578⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_26]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 315) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[27]!).2.val) = (1618829578, 261070109) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1618829578, 261070109⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_27]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 316) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[28]!).2.val) = (1399753701, 1692335411) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1399753701, 1692335411⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_28]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 317) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[29]!).2.val) = (1692335411, 747729946) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1692335411, 747729946⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_29]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 318) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[30]!).2.val) = (1150072909, 950473072) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1150072909, 950473072⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_30]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk09Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 319) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[31]!).2.val) = (950473072, 997410738) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨950473072, 997410738⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk09Certificate.entry_31]
  exact R17TableAChunk09Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsA09ChunkPower
