import AspisR1QueryGeometryActual.Funs
import R17TableAChunk03Certificate

set_option autoImplicit false

namespace R17NarrowFunsA03ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 96) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[0]!).2.val) = (405858396, 413054922) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨405858396, 413054922⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_00_zPow

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 97) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[1]!).2.val) = (413054922, 1741625251) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨413054922, 1741625251⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_01_zPow

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 98) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[2]!).2.val) = (1343434959, 1740046445) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1343434959, 1740046445⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_02_zPow

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 99) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[3]!).2.val) = (1740046445, 804048688) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1740046445, 804048688⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_03_zPow

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 100) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[4]!).2.val) = (1697594322, 1318496168) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1697594322, 1318496168⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_04_zPow

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 101) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[5]!).2.val) = (1318496168, 449889325) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1318496168, 449889325⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_05_zPow

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 102) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[6]!).2.val) = (1908257733, 904587623) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1908257733, 904587623⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_06_zPow

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 103) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[7]!).2.val) = (904587623, 239225914) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨904587623, 239225914⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_07_zPow

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 104) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[8]!).2.val) = (1569205000, 1460088186) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1569205000, 1460088186⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_08_zPow

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 105) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[9]!).2.val) = (1460088186, 578278647) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1460088186, 578278647⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_09_zPow

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 106) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[10]!).2.val) = (742503567, 20511103) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨742503567, 20511103⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_10_zPow

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 107) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[11]!).2.val) = (20511103, 1404980080) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨20511103, 1404980080⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_11_zPow

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 108) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[12]!).2.val) = (924436841, 179213100) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨924436841, 179213100⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_12_zPow

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 109) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[13]!).2.val) = (179213100, 1223046806) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨179213100, 1223046806⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_13_zPow

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 110) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[14]!).2.val) = (776651208, 1692488596) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨776651208, 1692488596⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_14_zPow

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 111) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[15]!).2.val) = (1692488596, 1370832439) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1692488596, 1370832439⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_15_zPow

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 112) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[16]!).2.val) = (685109443, 308131929) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨685109443, 308131929⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_16_zPow

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 113) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[17]!).2.val) = (308131929, 1462374204) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨308131929, 1462374204⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_17_zPow

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 114) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[18]!).2.val) = (1418607411, 1674242439) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1418607411, 1674242439⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_18_zPow

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 115) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[19]!).2.val) = (1674242439, 728876236) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1674242439, 728876236⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_19_zPow

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 116) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[20]!).2.val) = (1831338762, 818744620) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1831338762, 818744620⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_20_zPow

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 117) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[21]!).2.val) = (818744620, 316144885) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨818744620, 316144885⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_21_zPow

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 118) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[22]!).2.val) = (136027637, 84984741) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨136027637, 84984741⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_22_zPow

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 119) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[23]!).2.val) = (84984741, 2011456010) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨84984741, 2011456010⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_23_zPow

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 120) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[24]!).2.val) = (832857621, 1800803482) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨832857621, 1800803482⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_24_zPow

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 121) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[25]!).2.val) = (1800803482, 1314626026) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1800803482, 1314626026⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_25_zPow

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 122) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[26]!).2.val) = (1029184762, 1463990705) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1029184762, 1463990705⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_26_zPow

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 123) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[27]!).2.val) = (1463990705, 1118298885) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1463990705, 1118298885⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_27_zPow

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 124) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[28]!).2.val) = (1026246497, 462715637) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1026246497, 462715637⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_28_zPow

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 125) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[29]!).2.val) = (462715637, 1121237150) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨462715637, 1121237150⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_29_zPow

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 126) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[30]!).2.val) = (1630230719, 432660073) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1630230719, 432660073⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_30_zPow

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 127) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[31]!).2.val) = (432660073, 517252928) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨432660073, 517252928⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk03Certificate.entry_31_zPow

#print axioms cell_31_circle_power

end R17NarrowFunsA03ChunkPower
