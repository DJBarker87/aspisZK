import AspisR1QueryGeometryActual.Funs
import R17TableBChunk07Certificate

set_option autoImplicit false

namespace R17NarrowFunsB07ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 224) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[0]!).2.val) = (347749121, 1576860820) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨347749121, 1576860820⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_00]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 225) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[1]!).2.val) = (1986804722, 1373191730) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1986804722, 1373191730⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_01]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 226) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[2]!).2.val) = (1616101075, 811514491) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1616101075, 811514491⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_02]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 227) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[3]!).2.val) = (147800194, 1069151092) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨147800194, 1069151092⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_03]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 228) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[4]!).2.val) = (1565145988, 1765289675) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1565145988, 1765289675⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_04]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 229) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[5]!).2.val) = (365445058, 1099441367) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨365445058, 1099441367⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_05]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 230) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[6]!).2.val) = (920245660, 938576836) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨920245660, 938576836⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_06]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 231) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[7]!).2.val) = (204640856, 2040419027) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨204640856, 2040419027⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_07]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 232) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[8]!).2.val) = (1213375404, 771547637) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1213375404, 771547637⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_08]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 233) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[9]!).2.val) = (2064624001, 245417806) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2064624001, 245417806⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_09]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 234) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[10]!).2.val) = (494233883, 1403803427) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨494233883, 1403803427⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_10]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 235) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[11]!).2.val) = (1661270250, 1697085245) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1661270250, 1697085245⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_11]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 236) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[12]!).2.val) = (818224288, 1972399941) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨818224288, 1972399941⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_12]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 237) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[13]!).2.val) = (513998937, 202899553) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨513998937, 202899553⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_13]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 238) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[14]!).2.val) = (1757257503, 734249953) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1757257503, 734249953⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_14]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 239) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[15]!).2.val) = (1601634968, 1790370824) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1601634968, 1790370824⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_15]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 240) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[16]!).2.val) = (1829052821, 673049321) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1829052821, 673049321⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_16]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 241) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[17]!).2.val) = (1765843037, 2085683345) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1765843037, 2085683345⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_17]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 242) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[18]!).2.val) = (1213735332, 1357695652) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1213735332, 1357695652⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_18]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 243) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[19]!).2.val) = (1332929929, 2095879383) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1332929929, 2095879383⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_19]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 244) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[20]!).2.val) = (914918274, 1369105915) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨914918274, 1369105915⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_20]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 245) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[21]!).2.val) = (1478304746, 406667278) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1478304746, 406667278⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_21]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 246) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[22]!).2.val) = (919065681, 1216872295) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨919065681, 1216872295⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_22]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 247) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[23]!).2.val) = (1932017562, 1757637245) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1932017562, 1757637245⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_23]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 248) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[24]!).2.val) = (44588143, 2058311453) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨44588143, 2058311453⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_24]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 249) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[25]!).2.val) = (888152082, 1321895104) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨888152082, 1321895104⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_25]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 250) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[26]!).2.val) = (1408222478, 1721187542) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1408222478, 1721187542⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_26]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 251) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[27]!).2.val) = (210392081, 157752587) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨210392081, 157752587⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_27]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 252) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[28]!).2.val) = (1444319707, 1095294811) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1444319707, 1095294811⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_28]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 253) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[29]!).2.val) = (1540140142, 751979754) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1540140142, 751979754⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_29]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 254) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[30]!).2.val) = (570004307, 1164891669) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨570004307, 1164891669⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_30]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk07Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 255) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[31]!).2.val) = (1090698404, 2001864991) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1090698404, 2001864991⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk07Certificate.entry_31]
  exact R17TableBChunk07Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB07ChunkPower
