import AspisR1QueryGeometryActual.Funs
import R17TableBChunk13Certificate

set_option autoImplicit false

namespace R17NarrowFunsB13ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 416) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[0]!).2.val) = (1984370174, 548484416) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1984370174, 548484416⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_00]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 417) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[1]!).2.val) = (1760363481, 2129820178) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1760363481, 2129820178⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_01]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 418) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[2]!).2.val) = (1997990904, 355093967) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1997990904, 355093967⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_02]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 419) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[3]!).2.val) = (1980954341, 561676940) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1980954341, 561676940⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_03]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 420) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[4]!).2.val) = (207319829, 330698049) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨207319829, 330698049⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_04]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 421) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[5]!).2.val) = (480315830, 137067372) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨480315830, 137067372⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_05]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 422) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[6]!).2.val) = (1608197410, 953495473) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1608197410, 953495473⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_06]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 423) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[7]!).2.val) = (1433755461, 316564196) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1433755461, 316564196⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_07]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 424) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[8]!).2.val) = (591304555, 68989614) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨591304555, 68989614⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_08]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 425) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[9]!).2.val) = (569540672, 885330917) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨569540672, 885330917⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_09]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 426) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[10]!).2.val) = (865056590, 1396323689) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨865056590, 1396323689⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_10]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 427) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[11]!).2.val) = (237150930, 715611246) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨237150930, 715611246⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_11]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 428) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[12]!).2.val) = (1167250594, 1854887903) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1167250594, 1854887903⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_12]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 429) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[13]!).2.val) = (112696124, 268389163) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨112696124, 268389163⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_13]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 430) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[14]!).2.val) = (719959488, 88680757) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨719959488, 88680757⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_14]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 431) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[15]!).2.val) = (498135791, 1918711876) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨498135791, 1918711876⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_15]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 432) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[16]!).2.val) = (854984042, 63484416) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨854984042, 63484416⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_16]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 433) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[17]!).2.val) = (512573355, 559650698) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨512573355, 559650698⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_17]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 434) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[18]!).2.val) = (450129036, 2130393939) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨450129036, 2130393939⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_18]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 435) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[19]!).2.val) = (934129539, 1082077994) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨934129539, 1082077994⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_19]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 436) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[20]!).2.val) = (787391422, 234435571) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨787391422, 234435571⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_20]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 437) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[21]!).2.val) = (808165703, 1317710352) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨808165703, 1317710352⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_21]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 438) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[22]!).2.val) = (92769725, 1231653419) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨92769725, 1231653419⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_22]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 439) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[23]!).2.val) = (1699669774, 817702196) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1699669774, 817702196⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_23]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 440) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[24]!).2.val) = (1696657789, 2121958423) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1696657789, 2121958423⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_24]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 441) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[25]!).2.val) = (181669902, 1993442275) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨181669902, 1993442275⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_25]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 442) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[26]!).2.val) = (1735177288, 1041858071) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1735177288, 1041858071⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_26]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 443) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[27]!).2.val) = (265914936, 748543764) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨265914936, 748543764⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_27]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 444) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[28]!).2.val) = (2077839401, 709133143) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2077839401, 709133143⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_28]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 445) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[29]!).2.val) = (479770865, 2027287932) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨479770865, 2027287932⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_29]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 446) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[30]!).2.val) = (1742529025, 278083478) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1742529025, 278083478⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_30]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 447) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[31]!).2.val) = (1334313253, 1249554241) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1334313253, 1249554241⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk13Certificate.entry_31]
  exact R17TableBChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB13ChunkPower
