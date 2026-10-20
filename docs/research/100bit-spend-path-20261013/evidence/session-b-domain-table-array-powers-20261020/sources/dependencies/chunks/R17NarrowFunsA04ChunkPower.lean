import AspisR1QueryGeometryActual.Funs
import R17TableAChunk04Certificate

set_option autoImplicit false

namespace R17NarrowFunsA04ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 128) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[0]!).2.val) = (789199007, 265368403) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨789199007, 265368403⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_00]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 129) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[1]!).2.val) = (265368403, 1358284640) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨265368403, 1358284640⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_01]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 130) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[2]!).2.val) = (905527003, 2103042246) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨905527003, 2103042246⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_02]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 131) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[3]!).2.val) = (2103042246, 1241956644) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2103042246, 1241956644⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_03]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 132) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[4]!).2.val) = (966963960, 791773240) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨966963960, 791773240⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_04]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 133) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[5]!).2.val) = (791773240, 1180519687) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨791773240, 1180519687⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_05]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 134) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[6]!).2.val) = (429418708, 1721759118) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨429418708, 1721759118⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_06]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 135) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[7]!).2.val) = (1721759118, 1718064939) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1721759118, 1718064939⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_07]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 136) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[8]!).2.val) = (226919109, 591805476) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨226919109, 591805476⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_08]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 137) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[9]!).2.val) = (591805476, 1920564538) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨591805476, 1920564538⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_09]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 138) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[10]!).2.val) = (1601482956, 1555011007) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1601482956, 1555011007⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_10]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 139) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[11]!).2.val) = (1555011007, 546000691) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1555011007, 546000691⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_11]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 140) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[12]!).2.val) = (925678133, 1851895798) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨925678133, 1851895798⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_12]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 141) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[13]!).2.val) = (1851895798, 1221805514) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1851895798, 1221805514⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_13]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 142) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[14]!).2.val) = (890643854, 2061547316) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨890643854, 2061547316⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_14]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 143) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[15]!).2.val) = (2061547316, 1256839793) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2061547316, 1256839793⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_15]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 144) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[16]!).2.val) = (2045776109, 764411913) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2045776109, 764411913⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_16]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 145) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[17]!).2.val) = (764411913, 101707538) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨764411913, 101707538⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_17]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 146) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[18]!).2.val) = (142321536, 2005775263) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨142321536, 2005775263⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_18]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 147) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[19]!).2.val) = (2005775263, 2005162111) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2005775263, 2005162111⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_19]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 148) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[20]!).2.val) = (852511271, 383685221) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨852511271, 383685221⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_20]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 149) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[21]!).2.val) = (383685221, 1294972376) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨383685221, 1294972376⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_21]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 150) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[22]!).2.val) = (1850100142, 606004238) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1850100142, 606004238⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_22]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 151) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[23]!).2.val) = (606004238, 297383505) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨606004238, 297383505⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_23]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 152) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[24]!).2.val) = (1988413837, 422428418) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1988413837, 422428418⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_24]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 153) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[25]!).2.val) = (422428418, 159069810) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨422428418, 159069810⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_25]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 154) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[26]!).2.val) = (1145573298, 2059018920) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1145573298, 2059018920⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_26]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 155) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[27]!).2.val) = (2059018920, 1001910349) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2059018920, 1001910349⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_27]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 156) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[28]!).2.val) = (1024200565, 2131726269) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1024200565, 2131726269⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_28]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 157) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[29]!).2.val) = (2131726269, 1123283082) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2131726269, 1123283082⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_29]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 158) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[30]!).2.val) = (1335475227, 1076118019) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1335475227, 1076118019⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_30]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 159) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[31]!).2.val) = (1076118019, 812008420) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1076118019, 812008420⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk04Certificate.entry_31]
  exact R17TableAChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsA04ChunkPower
