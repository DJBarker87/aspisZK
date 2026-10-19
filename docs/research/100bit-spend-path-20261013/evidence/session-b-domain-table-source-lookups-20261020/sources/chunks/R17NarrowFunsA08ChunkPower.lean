import AspisR1QueryGeometryActual.Funs
import R17TableAChunk08Certificate

set_option autoImplicit false

namespace R17NarrowFunsA08ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 256) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[0]!).2.val) = (785785922, 1967683322) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨785785922, 1967683322⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_00]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 257) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[1]!).2.val) = (1967683322, 1361697725) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1967683322, 1361697725⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_01]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 258) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[2]!).2.val) = (1302242334, 693913202) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1302242334, 693913202⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_02]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 259) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[3]!).2.val) = (693913202, 845241313) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨693913202, 845241313⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_03]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 260) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[4]!).2.val) = (1932511129, 687696804) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1932511129, 687696804⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_04]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 261) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[5]!).2.val) = (687696804, 214972518) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨687696804, 214972518⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_05]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 262) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[6]!).2.val) = (429857837, 1376073165) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨429857837, 1376073165⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_06]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 263) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[7]!).2.val) = (1376073165, 1717625810) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1376073165, 1717625810⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_07]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 264) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[8]!).2.val) = (778346524, 2089805548) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨778346524, 2089805548⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_08]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 265) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[9]!).2.val) = (2089805548, 1369137123) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2089805548, 1369137123⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_09]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 266) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[10]!).2.val) = (1132767988, 594038315) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1132767988, 594038315⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_10]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 267) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[11]!).2.val) = (594038315, 1014715659) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨594038315, 1014715659⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_11]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 268) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[12]!).2.val) = (2078867071, 276497442) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2078867071, 276497442⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_12]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 269) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[13]!).2.val) = (276497442, 68616576) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨276497442, 68616576⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_13]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 270) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[14]!).2.val) = (22088804, 47256722) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨22088804, 47256722⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_14]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 271) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[15]!).2.val) = (47256722, 2125394843) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨47256722, 2125394843⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_15]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 272) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[16]!).2.val) = (2089806413, 155403522) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2089806413, 155403522⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_16]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 273) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[17]!).2.val) = (155403522, 57677234) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨155403522, 57677234⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_17]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 274) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[18]!).2.val) = (396887507, 760876211) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨396887507, 760876211⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_18]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 275) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[19]!).2.val) = (760876211, 1750596140) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨760876211, 1750596140⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_19]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 276) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[20]!).2.val) = (1005915392, 1867478512) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1005915392, 1867478512⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_20]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 277) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[21]!).2.val) = (1867478512, 1141568255) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1867478512, 1141568255⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_21]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 278) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[22]!).2.val) = (1098427204, 880292698) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1098427204, 880292698⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_22]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 279) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[23]!).2.val) = (880292698, 1049056443) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨880292698, 1049056443⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_23]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 280) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[24]!).2.val) = (10571466, 1530894063) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨10571466, 1530894063⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_24]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 281) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[25]!).2.val) = (1530894063, 2136912181) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1530894063, 2136912181⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_25]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 282) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[26]!).2.val) = (1927076832, 605215390) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1927076832, 605215390⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_26]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 283) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[27]!).2.val) = (605215390, 220406815) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨605215390, 220406815⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_27]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 284) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[28]!).2.val) = (1461025413, 1421466600) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1461025413, 1421466600⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_28]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 285) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[29]!).2.val) = (1421466600, 686458234) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1421466600, 686458234⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_29]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 286) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[30]!).2.val) = (725035983, 816938404) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨725035983, 816938404⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_30]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk08Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 287) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[31]!).2.val) = (816938404, 1422447664) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨816938404, 1422447664⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk08Certificate.entry_31]
  exact R17TableAChunk08Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsA08ChunkPower
