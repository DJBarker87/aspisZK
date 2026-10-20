import AspisR1QueryGeometryActual.Funs
import R17TableBChunk11Certificate

set_option autoImplicit false

namespace R17NarrowFunsB11ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 352) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[0]!).2.val) = (528497962, 2048433423) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨528497962, 2048433423⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_00]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 353) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[1]!).2.val) = (668998651, 249239603) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨668998651, 249239603⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_01]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 354) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[2]!).2.val) = (58617043, 693726782) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨58617043, 693726782⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_02]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 355) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[3]!).2.val) = (1475204899, 1648029352) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1475204899, 1648029352⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_03]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 356) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[4]!).2.val) = (1576856103, 1461690978) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1576856103, 1461690978⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_04]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 357) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[5]!).2.val) = (1488450015, 601243945) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1488450015, 601243945⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_05]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 358) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[6]!).2.val) = (799756877, 308500462) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨799756877, 308500462⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_06]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 359) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[7]!).2.val) = (571821609, 1489087773) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨571821609, 1489087773⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_07]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 360) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[8]!).2.val) = (1029245122, 1158447597) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1029245122, 1158447597⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_08]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 361) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[9]!).2.val) = (1058730422, 1950344727) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1058730422, 1950344727⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_09]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 362) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[10]!).2.val) = (1210158521, 1506582976) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1210158521, 1506582976⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_10]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 363) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[11]!).2.val) = (826608058, 2050139532) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨826608058, 2050139532⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_11]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 364) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[12]!).2.val) = (2076036242, 130048956) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2076036242, 130048956⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_12]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 365) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[13]!).2.val) = (185991083, 1518281638) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨185991083, 1518281638⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_13]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 366) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[14]!).2.val) = (1797669071, 2141355836) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1797669071, 2141355836⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_14]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 367) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[15]!).2.val) = (413934600, 1586830163) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨413934600, 1586830163⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_15]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 368) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[16]!).2.val) = (845078094, 149898124) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨845078094, 149898124⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_16]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 369) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[17]!).2.val) = (674296139, 317324829) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨674296139, 317324829⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_17]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 370) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[18]!).2.val) = (25637092, 421692094) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨25637092, 421692094⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_18]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 371) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[19]!).2.val) = (970891652, 610465777) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨970891652, 610465777⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_19]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 372) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[20]!).2.val) = (647843950, 788293466) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨647843950, 788293466⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_20]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 373) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[21]!).2.val) = (148228362, 590602766) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨148228362, 590602766⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_21]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 374) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[22]!).2.val) = (69829270, 1352453515) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨69829270, 1352453515⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_22]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 375) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[23]!).2.val) = (1683233817, 1287709593) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1683233817, 1287709593⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_23]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 376) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[24]!).2.val) = (887385898, 608769478) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨887385898, 608769478⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_24]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 377) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[25]!).2.val) = (1269707845, 1452388824) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1269707845, 1452388824⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_25]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 378) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[26]!).2.val) = (852276839, 226974950) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨852276839, 226974950⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_26]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 379) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[27]!).2.val) = (412577235, 1997534047) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨412577235, 1997534047⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_27]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 380) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[28]!).2.val) = (1615674956, 1808914239) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1615674956, 1808914239⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_28]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 381) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[29]!).2.val) = (406123904, 764760651) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨406123904, 764760651⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_29]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 382) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[30]!).2.val) = (2126452532, 708823575) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2126452532, 708823575⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_30]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 383) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[31]!).2.val) = (1991612315, 1875574124) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1991612315, 1875574124⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk11Certificate.entry_31]
  exact R17TableBChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB11ChunkPower
