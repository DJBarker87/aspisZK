import AspisR1QueryGeometryActual.Funs
import R17TableAChunk01Certificate

set_option autoImplicit false

namespace R17NarrowFunsA01ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 32) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[0]!).2.val) = (1319895764, 573785706) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1319895764, 573785706⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_00_zPow

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 33) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[1]!).2.val) = (573785706, 827587883) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨573785706, 827587883⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_01_zPow

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 34) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[2]!).2.val) = (614428895, 566940551) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨614428895, 566940551⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_02_zPow

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 35) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[3]!).2.val) = (566940551, 1533054752) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨566940551, 1533054752⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_03_zPow

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 36) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[4]!).2.val) = (1614159808, 1309336248) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1614159808, 1309336248⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_04_zPow

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 37) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[5]!).2.val) = (1309336248, 533323839) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1309336248, 533323839⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_05_zPow

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 38) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[6]!).2.val) = (20753985, 1635511764) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨20753985, 1635511764⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_06_zPow

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 39) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[7]!).2.val) = (1635511764, 2126729662) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1635511764, 2126729662⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_07_zPow

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 40) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[8]!).2.val) = (1685341984, 359481912) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1685341984, 359481912⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_08_zPow

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 41) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[9]!).2.val) = (359481912, 462141663) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨359481912, 462141663⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_09_zPow

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 42) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[10]!).2.val) = (1152154081, 2106306808) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1152154081, 2106306808⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_10_zPow

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 43) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[11]!).2.val) = (2106306808, 995329566) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2106306808, 995329566⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_11_zPow

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 44) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[12]!).2.val) = (638582271, 300788326) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨638582271, 300788326⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_12_zPow

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 45) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[13]!).2.val) = (300788326, 1508901376) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨300788326, 1508901376⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_13_zPow

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 46) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[14]!).2.val) = (1412610045, 1446210525) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1412610045, 1446210525⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_14_zPow

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 47) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[15]!).2.val) = (1446210525, 734873602) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1446210525, 734873602⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_15_zPow

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 48) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[16]!).2.val) = (1747362177, 1031300071) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1747362177, 1031300071⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_16_zPow

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 49) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[17]!).2.val) = (1031300071, 400121470) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1031300071, 400121470⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_17_zPow

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 50) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[18]!).2.val) = (45393311, 1630721361) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨45393311, 1630721361⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_18_zPow

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 51) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[19]!).2.val) = (1630721361, 2102090336) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1630721361, 2102090336⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_19_zPow

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 52) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[20]!).2.val) = (628786761, 140902127) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨628786761, 140902127⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_20_zPow

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 53) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[21]!).2.val) = (140902127, 1518696886) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨140902127, 1518696886⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_21_zPow

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 54) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[22]!).2.val) = (1117531616, 1012065003) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1117531616, 1012065003⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_22_zPow

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 55) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[23]!).2.val) = (1012065003, 1029952031) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1012065003, 1029952031⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_23_zPow

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 56) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[24]!).2.val) = (320524274, 1536842560) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨320524274, 1536842560⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_24_zPow

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 57) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[25]!).2.val) = (1536842560, 1826959373) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1536842560, 1826959373⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_25_zPow

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 58) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[26]!).2.val) = (362376885, 1168590975) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨362376885, 1168590975⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_26_zPow

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 59) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[27]!).2.val) = (1168590975, 1785106762) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1168590975, 1785106762⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_27_zPow

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 60) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[28]!).2.val) = (1108016105, 252024370) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1108016105, 252024370⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_28_zPow

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 61) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[29]!).2.val) = (252024370, 1039467542) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨252024370, 1039467542⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_29_zPow

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 62) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[30]!).2.val) = (1225642256, 1294224634) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1225642256, 1294224634⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_30_zPow

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (R17TableAChunk01Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 63) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[31]!).2.val) = (1294224634, 921841391) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1294224634, 921841391⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  exact R17TableAChunk01Certificate.entry_31_zPow

#print axioms cell_31_circle_power

end R17NarrowFunsA01ChunkPower
