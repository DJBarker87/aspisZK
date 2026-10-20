import AspisR1QueryGeometryActual.Funs
import R17TableBChunk05Certificate

set_option autoImplicit false

namespace R17NarrowFunsB05ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 160) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[0]!).2.val) = (263253631, 1948074535) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨263253631, 1948074535⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_00]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 161) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[1]!).2.val) = (804296458, 213396278) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨804296458, 213396278⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_01]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 162) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[2]!).2.val) = (153716819, 2054656334) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨153716819, 2054656334⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_02]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 163) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[3]!).2.val) = (2104095544, 1435777142) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2104095544, 1435777142⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_03]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 164) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[4]!).2.val) = (1479292912, 403634516) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1479292912, 403634516⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_04]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 165) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[5]!).2.val) = (565878948, 1786880501) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨565878948, 1786880501⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_05]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 166) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[6]!).2.val) = (682480399, 799350698) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨682480399, 799350698⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_06]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 167) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[7]!).2.val) = (1340472519, 1675598842) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1340472519, 1675598842⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_07]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 168) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[8]!).2.val) = (735504938, 198004457) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨735504938, 198004457⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_08]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 169) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[9]!).2.val) = (848969192, 1414511411) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨848969192, 1414511411⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_09]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 170) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[10]!).2.val) = (2083960347, 2126322313) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2083960347, 2126322313⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_10]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 171) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[11]!).2.val) = (1209545065, 1852982367) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1209545065, 1852982367⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_11]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 172) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[12]!).2.val) = (386684296, 1363813538) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨386684296, 1363813538⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_12]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 173) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[13]!).2.val) = (1083568418, 725197280) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1083568418, 725197280⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_13]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 174) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[14]!).2.val) = (1439180125, 915904269) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1439180125, 915904269⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_14]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 175) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[15]!).2.val) = (1480502711, 1450760425) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1480502711, 1450760425⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_15]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 176) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[16]!).2.val) = (1488671228, 939868393) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1488671228, 939868393⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_16]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 177) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[17]!).2.val) = (1982402, 431614399) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1982402, 431614399⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_17]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 178) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[18]!).2.val) = (1542296538, 1163978019) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1542296538, 1163978019⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_18]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 179) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[19]!).2.val) = (1244152270, 498961107) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1244152270, 498961107⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_19]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 180) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[20]!).2.val) = (1362074261, 2047718881) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1362074261, 2047718881⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_20]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 181) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[21]!).2.val) = (563752921, 1285853654) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨563752921, 1285853654⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_21]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 182) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[22]!).2.val) = (1834599352, 1895440138) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1834599352, 1895440138⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_22]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 183) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[23]!).2.val) = (1662799443, 1810348412) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1662799443, 1810348412⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_23]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 184) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[24]!).2.val) = (474711937, 1020011657) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨474711937, 1020011657⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_24]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 185) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[25]!).2.val) = (1134947640, 394118266) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1134947640, 394118266⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_25]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 186) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[26]!).2.val) = (1739468984, 977169647) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1739468984, 977169647⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_26]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 187) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[27]!).2.val) = (227977990, 1816535211) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨227977990, 1816535211⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_27]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 188) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[28]!).2.val) = (836848068, 529120781) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨836848068, 529120781⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_28]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 189) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[29]!).2.val) = (210740911, 1280364462) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨210740911, 1280364462⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_29]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 190) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[30]!).2.val) = (581559614, 117257650) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨581559614, 117257650⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_30]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk05Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 191) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[31]!).2.val) = (510094092, 641201894) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨510094092, 641201894⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk05Certificate.entry_31]
  exact R17TableBChunk05Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB05ChunkPower
