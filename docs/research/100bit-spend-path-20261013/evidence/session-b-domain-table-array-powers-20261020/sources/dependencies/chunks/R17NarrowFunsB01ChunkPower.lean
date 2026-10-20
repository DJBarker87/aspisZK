import AspisR1QueryGeometryActual.Funs
import R17TableBChunk01Certificate

set_option autoImplicit false

namespace R17NarrowFunsB01ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 32) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[0]!).2.val) = (1389168750, 838891026) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1389168750, 838891026⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_00]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 33) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[1]!).2.val) = (1636834739, 1597012617) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1636834739, 1597012617⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_01]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 34) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[2]!).2.val) = (1454515876, 223346768) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1454515876, 223346768⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_02]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 35) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[3]!).2.val) = (1756352277, 1351837341) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1756352277, 1351837341⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_03]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 36) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[4]!).2.val) = (240698073, 476721530) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨240698073, 476721530⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_04]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 37) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[5]!).2.val) = (427864406, 1584676261) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨427864406, 1584676261⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_05]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 38) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[6]!).2.val) = (185070104, 2052638160) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨185070104, 2052638160⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_06]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 39) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[7]!).2.val) = (1275605666, 2095784385) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1275605666, 2095784385⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_07]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 40) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[8]!).2.val) = (296310565, 109983397) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨296310565, 109983397⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_08]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 41) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[9]!).2.val) = (72206514, 1289188236) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨72206514, 1289188236⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_09]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 42) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[10]!).2.val) = (709836333, 1607887694) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨709836333, 1607887694⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_10]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 43) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[11]!).2.val) = (1513780754, 2116268837) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1513780754, 2116268837⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_11]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 44) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[12]!).2.val) = (472230981, 1127178204) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨472230981, 1127178204⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_12]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 45) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[13]!).2.val) = (337258740, 799789868) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨337258740, 799789868⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_13]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 46) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[14]!).2.val) = (954563443, 1672118401) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨954563443, 1672118401⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_14]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 47) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[15]!).2.val) = (1873486026, 204075296) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1873486026, 204075296⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_15]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 48) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[16]!).2.val) = (13191618, 303576968) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨13191618, 303576968⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_16]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 49) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[17]!).2.val) = (1514546700, 482975034) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1514546700, 482975034⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_17]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 50) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[18]!).2.val) = (1820378488, 1427649814) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1820378488, 1427649814⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_18]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 51) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[19]!).2.val) = (20135698, 907128133) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨20135698, 907128133⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_19]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 52) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[20]!).2.val) = (1363572456, 1209117074) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1363572456, 1209117074⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_20]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 53) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[21]!).2.val) = (1184836041, 810606909) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1184836041, 810606909⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_21]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 54) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[22]!).2.val) = (483972604, 51373831) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨483972604, 51373831⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_22]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 55) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[23]!).2.val) = (309323555, 1207665785) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨309323555, 1207665785⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_23]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 56) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[24]!).2.val) = (1577483195, 846841358) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1577483195, 846841358⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_24]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 57) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[25]!).2.val) = (472215603, 885906123) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨472215603, 885906123⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_25]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 58) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[26]!).2.val) = (1804344690, 999799715) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1804344690, 999799715⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_26]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 59) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[27]!).2.val) = (175617284, 1795732353) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨175617284, 1795732353⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_27]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 60) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[28]!).2.val) = (389608651, 1555639321) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨389608651, 1555639321⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_28]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 61) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[29]!).2.val) = (594200728, 1849269846) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨594200728, 1849269846⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_29]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 62) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[30]!).2.val) = (329547558, 1589038929) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨329547558, 1589038929⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_30]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 63) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[31]!).2.val) = (2118815938, 2129511119) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2118815938, 2129511119⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk01Certificate.entry_31]
  exact R17TableBChunk01Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB01ChunkPower
