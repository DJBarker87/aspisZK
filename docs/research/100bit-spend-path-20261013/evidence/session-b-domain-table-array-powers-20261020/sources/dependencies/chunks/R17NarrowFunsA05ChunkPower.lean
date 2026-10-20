import AspisR1QueryGeometryActual.Funs
import R17TableAChunk05Certificate

set_option autoImplicit false

namespace R17NarrowFunsA05ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 160) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[0]!).2.val) = (430897376, 660937846) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨430897376, 660937846⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_00]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 161) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[1]!).2.val) = (660937846, 1716586271) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨660937846, 1716586271⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_01]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 162) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[2]!).2.val) = (178995476, 298519990) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨178995476, 298519990⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_02]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 163) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[3]!).2.val) = (298519990, 1968488171) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨298519990, 1968488171⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_03]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 164) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[4]!).2.val) = (1413092576, 2009537990) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1413092576, 2009537990⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_04]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 165) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[5]!).2.val) = (2009537990, 734391071) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2009537990, 734391071⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_05]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 166) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[6]!).2.val) = (424922113, 74654605) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨424922113, 74654605⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_06]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 167) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[7]!).2.val) = (74654605, 1722561534) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨74654605, 1722561534⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_07]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 168) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[8]!).2.val) = (665291814, 184778403) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨665291814, 184778403⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_08]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 169) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[9]!).2.val) = (184778403, 1482191833) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨184778403, 1482191833⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_09]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 170) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[10]!).2.val) = (90485419, 2034131803) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨90485419, 2034131803⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_10]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 171) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[11]!).2.val) = (2034131803, 2056998228) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2034131803, 2056998228⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_11]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 172) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[12]!).2.val) = (1608154088, 833338502) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1608154088, 833338502⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_12]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 173) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[13]!).2.val) = (833338502, 539329559) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨833338502, 539329559⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_13]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 174) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[14]!).2.val) = (473403782, 542036433) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨473403782, 542036433⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_14]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 175) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[15]!).2.val) = (542036433, 1674079865) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨542036433, 1674079865⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_15]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 176) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[16]!).2.val) = (955512264, 573921543) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨955512264, 573921543⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_16]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 177) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[17]!).2.val) = (573921543, 1191971383) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨573921543, 1191971383⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_17]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 178) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[18]!).2.val) = (661117737, 832530753) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨661117737, 832530753⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_18]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 179) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[19]!).2.val) = (832530753, 1486365910) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨832530753, 1486365910⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_19]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 180) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[20]!).2.val) = (251387545, 585003076) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨251387545, 585003076⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_20]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 181) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[21]!).2.val) = (585003076, 1896096102) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨585003076, 1896096102⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_21]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 182) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[22]!).2.val) = (661565914, 1221956578) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨661565914, 1221956578⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_22]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 183) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[23]!).2.val) = (1221956578, 1485917733) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1221956578, 1485917733⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_23]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 184) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[24]!).2.val) = (420922661, 1190171598) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨420922661, 1190171598⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_24]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 185) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[25]!).2.val) = (1190171598, 1726560986) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1190171598, 1726560986⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_25]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 186) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[26]!).2.val) = (746184711, 1733602777) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨746184711, 1733602777⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_26]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 187) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[27]!).2.val) = (1733602777, 1401298936) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1733602777, 1401298936⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_27]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 188) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[28]!).2.val) = (1717922210, 1653599957) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1717922210, 1653599957⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_28]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 189) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[29]!).2.val) = (1653599957, 429561437) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1653599957, 429561437⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_29]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 190) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[30]!).2.val) = (742148341, 1117355050) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨742148341, 1117355050⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_30]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 191) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[31]!).2.val) = (1117355050, 1405335306) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1117355050, 1405335306⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk05Certificate.entry_31]
  exact R17TableAChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsA05ChunkPower
