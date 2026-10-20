import AspisR1QueryGeometryActual.Funs
import R17TableBChunk12Certificate

set_option autoImplicit false

namespace R17NarrowFunsB12ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 384) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[0]!).2.val) = (1475016787, 1876816901) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1475016787, 1876816901⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_00]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 385) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[1]!).2.val) = (1065576003, 1260155159) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1065576003, 1260155159⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_01]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 386) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[2]!).2.val) = (150344386, 103390841) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨150344386, 103390841⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_02]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 387) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[3]!).2.val) = (1736259183, 993645757) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1736259183, 993645757⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_03]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 388) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[4]!).2.val) = (458199028, 2319221) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨458199028, 2319221⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_04]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 389) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[5]!).2.val) = (870734736, 2085864614) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨870734736, 2085864614⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_05]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 390) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[6]!).2.val) = (1388011311, 312501879) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1388011311, 312501879⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_06]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 391) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[7]!).2.val) = (1669933146, 467772885) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1669933146, 467772885⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_07]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 392) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[8]!).2.val) = (957870942, 905094216) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨957870942, 905094216⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_08]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 393) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[9]!).2.val) = (1326380755, 140779095) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1326380755, 140779095⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_09]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 394) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[10]!).2.val) = (1569000839, 48016228) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1569000839, 48016228⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_10]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 395) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[11]!).2.val) = (139466273, 1803083243) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨139466273, 1803083243⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_11]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 396) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[12]!).2.val) = (1681738638, 1038838871) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1681738638, 1038838871⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_12]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 397) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[13]!).2.val) = (1677449438, 113082240) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1677449438, 113082240⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_13]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 398) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[14]!).2.val) = (1490057922, 1016920220) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1490057922, 1016920220⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_14]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 399) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[15]!).2.val) = (1801577965, 1312472321) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1801577965, 1312472321⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_15]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 400) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[16]!).2.val) = (1214106985, 780900129) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1214106985, 780900129⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_16]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 401) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[17]!).2.val) = (1907575337, 569832496) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1907575337, 569832496⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_17]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 402) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[18]!).2.val) = (582949328, 603337063) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨582949328, 603337063⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_18]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 403) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[19]!).2.val) = (2009192190, 566186921) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2009192190, 566186921⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_19]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 404) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[20]!).2.val) = (236415000, 1220441885) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨236415000, 1220441885⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_20]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 405) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[21]!).2.val) = (1100966113, 642444966) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1100966113, 642444966⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_21]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 406) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[22]!).2.val) = (2086832175, 647027993) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2086832175, 647027993⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_22]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 407) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[23]!).2.val) = (442183737, 184219552) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨442183737, 184219552⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_23]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 408) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[24]!).2.val) = (891287480, 1172290213) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨891287480, 1172290213⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_24]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 409) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[25]!).2.val) = (398898618, 2000607785) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨398898618, 2000607785⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_25]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 410) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[26]!).2.val) = (991079294, 1616314544) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨991079294, 1616314544⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_26]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 411) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[27]!).2.val) = (641638338, 1769768123) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨641638338, 1769768123⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_27]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 412) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[28]!).2.val) = (1085445012, 1626464664) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1085445012, 1626464664⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_28]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 413) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[29]!).2.val) = (1917457045, 820650395) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1917457045, 820650395⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_29]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 414) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[30]!).2.val) = (1885905244, 1519283397) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1885905244, 1519283397⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_30]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk12Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 415) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[31]!).2.val) = (2098046315, 239316783) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2098046315, 239316783⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk12Certificate.entry_31]
  exact R17TableBChunk12Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB12ChunkPower
