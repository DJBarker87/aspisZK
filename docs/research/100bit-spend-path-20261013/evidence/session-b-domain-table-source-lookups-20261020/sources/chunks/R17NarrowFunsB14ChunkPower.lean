import AspisR1QueryGeometryActual.Funs
import R17TableBChunk14Certificate

set_option autoImplicit false

namespace R17NarrowFunsB14ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 448) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[0]!).2.val) = (1124768046, 299494314) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1124768046, 299494314⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_00]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 449) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[1]!).2.val) = (1055409021, 1215994438) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1055409021, 1215994438⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_01]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 450) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[2]!).2.val) = (333636023, 948573238) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨333636023, 948573238⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_02]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 451) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[3]!).2.val) = (548067276, 713948312) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨548067276, 713948312⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_03]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 452) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[4]!).2.val) = (1458581325, 1279621404) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1458581325, 1279621404⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_04]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 453) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[5]!).2.val) = (1873772561, 1110881047) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1873772561, 1110881047⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_05]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 454) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[6]!).2.val) = (994459063, 1883501554) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨994459063, 1883501554⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_06]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 455) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[7]!).2.val) = (308028775, 1118600221) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨308028775, 1118600221⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_07]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 456) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[8]!).2.val) = (1924483244, 1528988896) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1924483244, 1528988896⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_08]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 457) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[9]!).2.val) = (176039723, 154417691) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨176039723, 154417691⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_09]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 458) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[10]!).2.val) = (841695573, 113926739) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨841695573, 113926739⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_10]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 459) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[11]!).2.val) = (52691895, 801280851) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨52691895, 801280851⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_11]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 460) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[12]!).2.val) = (1212320872, 1495300507) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1212320872, 1495300507⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_12]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 461) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[13]!).2.val) = (540487422, 1063443989) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨540487422, 1063443989⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_13]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 462) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[14]!).2.val) = (1994468584, 1611997849) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1994468584, 1611997849⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_14]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 463) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[15]!).2.val) = (2119188567, 919124989) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2119188567, 919124989⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_15]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 464) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[16]!).2.val) = (1753543609, 1294275673) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1753543609, 1294275673⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_16]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 465) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[17]!).2.val) = (1908790330, 386453773) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1908790330, 386453773⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_17]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 466) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[18]!).2.val) = (1573749961, 753946855) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1573749961, 753946855⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_18]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 467) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[19]!).2.val) = (305276529, 1041544704) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨305276529, 1041544704⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_19]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 468) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[20]!).2.val) = (128738146, 457848703) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨128738146, 457848703⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_20]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 469) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[21]!).2.val) = (582395095, 1653762059) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨582395095, 1653762059⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_21]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 470) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[22]!).2.val) = (1104635206, 858881536) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1104635206, 858881536⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_22]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 471) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[23]!).2.val) = (1504303166, 365743328) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1504303166, 365743328⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_23]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 472) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[24]!).2.val) = (122809504, 181977862) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨122809504, 181977862⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_24]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 473) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[25]!).2.val) = (617875881, 1291144021) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨617875881, 1291144021⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_25]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 474) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[26]!).2.val) = (895013455, 284231781) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨895013455, 284231781⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_26]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 475) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[27]!).2.val) = (1880738855, 621634671) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1880738855, 621634671⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_27]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 476) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[28]!).2.val) = (1300871249, 1490001285) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1300871249, 1490001285⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_28]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 477) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[29]!).2.val) = (454136966, 941654637) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨454136966, 941654637⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_29]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 478) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[30]!).2.val) = (277472845, 620479805) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨277472845, 620479805⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_30]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 479) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[31]!).2.val) = (594888648, 735387713) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨594888648, 735387713⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk14Certificate.entry_31]
  exact R17TableBChunk14Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB14ChunkPower
