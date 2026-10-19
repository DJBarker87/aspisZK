import AspisR1QueryGeometryActual.Funs
import R17TableBChunk02Certificate

set_option autoImplicit false

namespace R17NarrowFunsB02ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 64) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[0]!).2.val) = (438833264, 1327019128) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨438833264, 1327019128⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_00]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 65) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[1]!).2.val) = (1247546638, 2100838754) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1247546638, 2100838754⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_01]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 66) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[2]!).2.val) = (287625694, 714961257) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨287625694, 714961257⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_02]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 67) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[3]!).2.val) = (155805646, 741953977) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨155805646, 741953977⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_03]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 68) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[4]!).2.val) = (694768587, 1335510377) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨694768587, 1335510377⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_04]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 69) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[5]!).2.val) = (414447487, 1660191568) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨414447487, 1660191568⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_05]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 70) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[6]!).2.val) = (1684659278, 1370520300) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1684659278, 1370520300⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_06]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 71) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[7]!).2.val) = (467042048, 2131513571) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨467042048, 2131513571⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_07]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 72) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[8]!).2.val) = (1384581133, 347627210) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1384581133, 347627210⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_08]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 73) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[9]!).2.val) = (1780251437, 1948453877) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1780251437, 1948453877⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_09]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 74) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[10]!).2.val) = (1421431969, 974095169) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1421431969, 974095169⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_10]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 75) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[11]!).2.val) = (961627178, 109177970) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨961627178, 109177970⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_11]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 76) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[12]!).2.val) = (1971845238, 153904061) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1971845238, 153904061⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_12]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 77) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[13]!).2.val) = (1188557366, 413281552) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1188557366, 413281552⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_13]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 78) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[14]!).2.val) = (1923810989, 1272366406) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1923810989, 1272366406⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_14]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 79) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[15]!).2.val) = (2063888815, 129056561) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2063888815, 129056561⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_15]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 80) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[16]!).2.val) = (1635360495, 1075839836) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1635360495, 1075839836⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_16]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 81) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[17]!).2.val) = (330063644, 208626297) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨330063644, 208626297⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_17]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 82) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[18]!).2.val) = (116111969, 557501350) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨116111969, 557501350⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_18]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 83) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[19]!).2.val) = (1516934575, 1368952111) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1516934575, 1368952111⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_19]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 84) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[20]!).2.val) = (2128165408, 1866558246) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2128165408, 1866558246⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_20]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 85) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[21]!).2.val) = (1794178592, 2103779454) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1794178592, 2103779454⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_21]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 86) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[22]!).2.val) = (720638041, 1133563860) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨720638041, 1133563860⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_22]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 87) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[23]!).2.val) = (1149377722, 1799983014) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1149377722, 1799983014⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_23]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 88) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[24]!).2.val) = (1004021208, 1870425365) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1004021208, 1870425365⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_24]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 89) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[25]!).2.val) = (706427304, 2023867009) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨706427304, 2023867009⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_25]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 90) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[26]!).2.val) = (991418403, 1480232698) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨991418403, 1480232698⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_26]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 91) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[27]!).2.val) = (1912203537, 1288850576) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1912203537, 1288850576⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_27]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 92) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[28]!).2.val) = (1461783988, 258760706) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1461783988, 258760706⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_28]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 93) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[29]!).2.val) = (1321308009, 1742025967) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1321308009, 1742025967⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_29]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 94) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[30]!).2.val) = (913493534, 2126309379) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨913493534, 2126309379⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_30]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk02Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 95) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[31]!).2.val) = (1963867290, 360941673) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1963867290, 360941673⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk02Certificate.entry_31]
  exact R17TableBChunk02Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB02ChunkPower
