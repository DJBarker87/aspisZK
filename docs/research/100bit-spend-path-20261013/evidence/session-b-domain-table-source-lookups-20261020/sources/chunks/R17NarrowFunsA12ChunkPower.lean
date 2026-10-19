import AspisR1QueryGeometryActual.Funs
import R17TableAChunk12Certificate

set_option autoImplicit false

namespace R17NarrowFunsA12ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 384) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[0]!).2.val) = (1421224217, 977701755) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1421224217, 977701755⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_00]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 385) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[1]!).2.val) = (977701755, 726259430) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨977701755, 726259430⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_01]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 386) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[2]!).2.val) = (1514835708, 825288080) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1514835708, 825288080⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_02]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 387) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[3]!).2.val) = (825288080, 632647939) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨825288080, 632647939⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_03]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 388) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[4]!).2.val) = (963110699, 493845922) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨963110699, 493845922⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_04]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 389) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[5]!).2.val) = (493845922, 1184372948) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨493845922, 1184372948⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_05]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 390) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[6]!).2.val) = (845600471, 1262183431) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨845600471, 1262183431⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_06]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 391) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[7]!).2.val) = (1262183431, 1301883176) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1262183431, 1301883176⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_07]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 392) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[8]!).2.val) = (779436839, 223436892) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨779436839, 223436892⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_08]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 393) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[9]!).2.val) = (223436892, 1368046808) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨223436892, 1368046808⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_09]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 394) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[10]!).2.val) = (1371651014, 244997852) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1371651014, 244997852⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_10]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 395) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[11]!).2.val) = (244997852, 775832633) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨244997852, 775832633⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_11]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 396) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[12]!).2.val) = (1368395169, 2122900869) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1368395169, 2122900869⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_12]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 397) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[13]!).2.val) = (2122900869, 779088478) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2122900869, 779088478⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_13]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 398) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[14]!).2.val) = (2039730200, 1811033336) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2039730200, 1811033336⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_14]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 399) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[15]!).2.val) = (1811033336, 107753447) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1811033336, 107753447⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_15]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 400) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[16]!).2.val) = (162657442, 1560528002) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨162657442, 1560528002⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_16]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 401) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[17]!).2.val) = (1560528002, 1984826205) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1560528002, 1984826205⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_17]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 402) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[18]!).2.val) = (1553098421, 1743803217) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1553098421, 1743803217⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_18]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 403) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[19]!).2.val) = (1743803217, 594385226) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1743803217, 594385226⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_19]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 404) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[20]!).2.val) = (24486645, 110112918) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨24486645, 110112918⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_20]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 405) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[21]!).2.val) = (110112918, 2122997002) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨110112918, 2122997002⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_21]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 406) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[22]!).2.val) = (1774553093, 1188070682) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1774553093, 1188070682⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_22]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 407) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[23]!).2.val) = (1188070682, 372930554) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1188070682, 372930554⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_23]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 408) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[24]!).2.val) = (534092016, 1184883641) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨534092016, 1184883641⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_24]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 409) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[25]!).2.val) = (1184883641, 1613391631) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1184883641, 1613391631⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_25]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 410) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[26]!).2.val) = (1045751413, 627353290) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1045751413, 627353290⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_26]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 411) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[27]!).2.val) = (627353290, 1101732234) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨627353290, 1101732234⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_27]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 412) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[28]!).2.val) = (903868214, 1028549284) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨903868214, 1028549284⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_28]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 413) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[29]!).2.val) = (1028549284, 1243615433) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1028549284, 1243615433⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_29]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 414) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[30]!).2.val) = (753759022, 1035405166) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨753759022, 1035405166⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_30]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 415) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[31]!).2.val) = (1035405166, 1393724625) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1035405166, 1393724625⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk12Certificate.entry_31]
  exact R17TableAChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsA12ChunkPower
