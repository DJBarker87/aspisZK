import AspisR1QueryGeometryActual.Funs
import R17TableBChunk03Certificate

set_option autoImplicit false

namespace R17NarrowFunsB03ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 96) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[0]!).2.val) = (377761958, 572545120) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨377761958, 572545120⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_00]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 97) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[1]!).2.val) = (1665396419, 574316292) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1665396419, 574316292⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_01]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 98) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[2]!).2.val) = (373302001, 1507699234) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨373302001, 1507699234⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_02]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 99) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[3]!).2.val) = (801595255, 1469213224) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨801595255, 1469213224⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_03]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 100) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[4]!).2.val) = (2051626085, 490550043) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2051626085, 490550043⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_04]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 101) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[5]!).2.val) = (996029127, 950036227) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨996029127, 950036227⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_05]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 102) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[6]!).2.val) = (1288641239, 397886040) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1288641239, 397886040⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_06]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 103) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[7]!).2.val) = (1264385016, 642191549) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1264385016, 642191549⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_07]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 104) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[8]!).2.val) = (324121113, 147452506) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨324121113, 147452506⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_08]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 105) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[9]!).2.val) = (1953213394, 1643851743) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1953213394, 1643851743⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_09]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 106) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[10]!).2.val) = (1002266725, 1988311862) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1002266725, 1988311862⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_10]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 107) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[11]!).2.val) = (991463235, 37546859) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨991463235, 37546859⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_11]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 108) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[12]!).2.val) = (1174950059, 1819822737) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1174950059, 1819822737⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_12]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 109) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[13]!).2.val) = (2040633711, 425180892) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2040633711, 425180892⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_13]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 110) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[14]!).2.val) = (213923363, 1047884791) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨213923363, 1047884791⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_14]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 111) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[15]!).2.val) = (328526853, 975070234) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨328526853, 975070234⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_15]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 112) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[16]!).2.val) = (1825664712, 501661179) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1825664712, 501661179⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_16]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 113) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[17]!).2.val) = (656109024, 1300585869) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨656109024, 1300585869⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_17]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 114) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[18]!).2.val) = (1145588529, 205357607) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1145588529, 205357607⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_18]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 115) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[19]!).2.val) = (2020371461, 1932572291) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2020371461, 1932572291⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_19]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 116) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[20]!).2.val) = (1466126871, 410615561) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1466126871, 410615561⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_20]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 117) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[21]!).2.val) = (1161400406, 1079422807) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1161400406, 1079422807⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_21]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 118) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[22]!).2.val) = (1209061891, 111843040) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1209061891, 111843040⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_22]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 119) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[23]!).2.val) = (952468088, 412399546) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨952468088, 412399546⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_23]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 120) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[24]!).2.val) = (640220223, 1154724018) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨640220223, 1154724018⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_24]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 121) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[25]!).2.val) = (471738157, 668712505) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨471738157, 668712505⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_25]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 122) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[26]!).2.val) = (1791257284, 457765379) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1791257284, 457765379⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_26]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 123) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[27]!).2.val) = (317467001, 1766420009) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨317467001, 1766420009⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_27]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 124) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[28]!).2.val) = (1581002989, 970103636) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1581002989, 970103636⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_28]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 125) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[29]!).2.val) = (632980202, 1582071541) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨632980202, 1582071541⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_29]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 126) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[30]!).2.val) = (88625828, 522726826) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨88625828, 522726826⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_30]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk03Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 127) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[31]!).2.val) = (914753278, 1399904526) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨914753278, 1399904526⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk03Certificate.entry_31]
  exact R17TableBChunk03Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB03ChunkPower
