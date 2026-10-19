import AspisR1QueryGeometryActual.Funs
import R17TableAChunk14Certificate

set_option autoImplicit false

namespace R17NarrowFunsA14ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 448) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[0]!).2.val) = (300510473, 181714998) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨300510473, 181714998⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_00]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 449) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[1]!).2.val) = (181714998, 1846973174) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨181714998, 1846973174⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_01]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 450) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[2]!).2.val) = (379559102, 697727211) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨379559102, 697727211⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_02]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 451) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[3]!).2.val) = (697727211, 1767924545) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨697727211, 1767924545⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_03]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 452) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[4]!).2.val) = (1556533402, 2005793122) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1556533402, 2005793122⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_04]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 453) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[5]!).2.val) = (2005793122, 590950245) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2005793122, 590950245⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_05]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 454) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[6]!).2.val) = (1694422100, 342104775) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1694422100, 342104775⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_06]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 455) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[7]!).2.val) = (342104775, 453061547) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨342104775, 453061547⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_07]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 456) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[8]!).2.val) = (512321057, 1271549173) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨512321057, 1271549173⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_08]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 457) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[9]!).2.val) = (1271549173, 1635162590) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1271549173, 1635162590⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_09]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 458) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[10]!).2.val) = (1502308947, 1936338240) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1502308947, 1936338240⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_10]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 459) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[11]!).2.val) = (1936338240, 645174700) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1936338240, 645174700⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_11]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 460) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[12]!).2.val) = (1988815881, 645751943) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1988815881, 645751943⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_12]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 461) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[13]!).2.val) = (645751943, 158667766) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨645751943, 158667766⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_13]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 462) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[14]!).2.val) = (675847432, 1010741234) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨675847432, 1010741234⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_14]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 463) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[15]!).2.val) = (1010741234, 1471636215) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1010741234, 1471636215⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_15]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 464) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[16]!).2.val) = (501721213, 24836471) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨501721213, 24836471⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_16]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 465) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[17]!).2.val) = (24836471, 1645762434) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨24836471, 1645762434⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_17]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 466) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[18]!).2.val) = (1358569314, 679273363) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1358569314, 679273363⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_18]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 467) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[19]!).2.val) = (679273363, 788914333) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨679273363, 788914333⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_19]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 468) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[20]!).2.val) = (1484722465, 1078988777) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1484722465, 1078988777⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_20]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 469) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[21]!).2.val) = (1078988777, 662761182) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1078988777, 662761182⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_21]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 470) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[22]!).2.val) = (277190863, 2137253840) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨277190863, 2137253840⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_22]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 471) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[23]!).2.val) = (2137253840, 1870292784) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2137253840, 1870292784⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_23]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 472) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[24]!).2.val) = (816500702, 1764869715) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨816500702, 1764869715⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_24]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 473) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[25]!).2.val) = (1764869715, 1330982945) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1764869715, 1330982945⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_25]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 474) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[26]!).2.val) = (1259936220, 2067445894) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1259936220, 2067445894⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_26]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 475) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[27]!).2.val) = (2067445894, 887547427) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2067445894, 887547427⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_27]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 476) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[28]!).2.val) = (1513273850, 1722220683) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1513273850, 1722220683⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_28]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 477) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[29]!).2.val) = (1722220683, 634209797) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1722220683, 634209797⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_29]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 478) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[30]!).2.val) = (1564688601, 591957108) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1564688601, 591957108⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_30]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 479) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[31]!).2.val) = (591957108, 582795046) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨591957108, 582795046⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk14Certificate.entry_31]
  exact R17TableAChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsA14ChunkPower
