import AspisR1QueryGeometryActual.Funs
import R17TableBChunk08Certificate

set_option autoImplicit false

namespace R17NarrowFunsB08ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 256) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[0]!).2.val) = (595037635, 2111542451) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨595037635, 2111542451⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_00]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 257) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[1]!).2.val) = (433157739, 937025459) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨433157739, 937025459⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_01]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 258) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[2]!).2.val) = (100684459, 1640456458) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨100684459, 1640456458⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_02]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 259) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[3]!).2.val) = (1936161103, 1911011743) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1936161103, 1911011743⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_03]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 260) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[4]!).2.val) = (2008329732, 1737289791) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2008329732, 1737289791⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_04]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 261) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[5]!).2.val) = (748970643, 485565246) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨748970643, 485565246⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_05]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 262) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[6]!).2.val) = (1220431105, 100455014) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1220431105, 100455014⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_06]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 263) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[7]!).2.val) = (1661468032, 1401616134) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1661468032, 1401616134⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_07]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 264) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[8]!).2.val) = (798338207, 2110850421) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨798338207, 2110850421⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_08]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 265) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[9]!).2.val) = (1219048271, 773733831) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1219048271, 773733831⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_09]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 266) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[10]!).2.val) = (1789955189, 505997887) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1789955189, 505997887⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_10]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 267) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[11]!).2.val) = (321157045, 133308492) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨321157045, 133308492⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_11]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 268) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[12]!).2.val) = (1819903752, 1929668715) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1819903752, 1929668715⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_12]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 269) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[13]!).2.val) = (354559414, 1412186133) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨354559414, 1412186133⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_13]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 270) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[14]!).2.val) = (683528853, 193776762) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨683528853, 193776762⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_14]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 271) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[15]!).2.val) = (1371420477, 247094679) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1371420477, 247094679⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_15]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 272) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[16]!).2.val) = (1964662320, 1382435771) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1964662320, 1382435771⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_16]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 273) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[17]!).2.val) = (1249682376, 474254021) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1249682376, 474254021⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_17]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 274) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[18]!).2.val) = (150937652, 383732090) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨150937652, 383732090⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_18]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 275) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[19]!).2.val) = (588173577, 946133187) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨588173577, 946133187⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_19]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 276) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[20]!).2.val) = (1250840269, 386418603) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1250840269, 386418603⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_20]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 277) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[21]!).2.val) = (122969455, 311337502) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨122969455, 311337502⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_21]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 278) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[22]!).2.val) = (332209582, 331411357) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨332209582, 331411357⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_22]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 279) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[23]!).2.val) = (2021756148, 85056840) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2021756148, 85056840⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_23]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 280) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[24]!).2.val) = (1631496031, 481893475) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1631496031, 481893475⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_24]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 281) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[25]!).2.val) = (964719250, 1012108343) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨964719250, 1012108343⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_25]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 282) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[26]!).2.val) = (168460970, 1615303811) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨168460970, 1615303811⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_26]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 283) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[27]!).2.val) = (1764389290, 1617898495) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1764389290, 1617898495⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_27]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 284) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[28]!).2.val) = (422755315, 374503008) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨422755315, 374503008⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_28]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 285) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[29]!).2.val) = (1920015819, 2017323756) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1920015819, 2017323756⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_29]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 286) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[30]!).2.val) = (719706205, 1755223690) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨719706205, 1755223690⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_30]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 287) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[31]!).2.val) = (1871020210, 2067959207) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1871020210, 2067959207⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk08Certificate.entry_31]
  exact R17TableBChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB08ChunkPower
