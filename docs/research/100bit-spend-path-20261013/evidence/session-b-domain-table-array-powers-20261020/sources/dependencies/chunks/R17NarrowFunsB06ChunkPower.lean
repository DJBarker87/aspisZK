import AspisR1QueryGeometryActual.Funs
import R17TableBChunk06Certificate

set_option autoImplicit false

namespace R17NarrowFunsB06ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 192) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[0]!).2.val) = (503318431, 730224775) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨503318431, 730224775⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_00]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 193) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[1]!).2.val) = (1571876055, 1388714234) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1571876055, 1388714234⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_01]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 194) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[2]!).2.val) = (1320977789, 1557620475) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1320977789, 1557620475⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_02]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 195) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[3]!).2.val) = (118365627, 1759509849) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨118365627, 1759509849⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_03]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 196) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[4]!).2.val) = (795729789, 119644040) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨795729789, 119644040⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_04]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 197) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[5]!).2.val) = (1386331726, 809207732) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1386331726, 809207732⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_05]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 198) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[6]!).2.val) = (753978456, 488132937) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨753978456, 488132937⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_06]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 199) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[7]!).2.val) = (662367932, 209372338) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨662367932, 209372338⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_07]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 200) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[8]!).2.val) = (940196297, 1361581394) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨940196297, 1361581394⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_08]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 201) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[9]!).2.val) = (550623242, 753832155) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨550623242, 753832155⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_09]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 202) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[10]!).2.val) = (6376089, 129509954) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨6376089, 129509954⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_10]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 203) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[11]!).2.val) = (446322859, 1580452721) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨446322859, 1580452721⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_11]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 204) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[12]!).2.val) = (1755458239, 1807540371) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1755458239, 1807540371⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_12]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 205) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[13]!).2.val) = (2142868905, 574364801) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2142868905, 574364801⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_13]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 206) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[14]!).2.val) = (1596830861, 2049034655) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1596830861, 2049034655⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_14]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 207) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[15]!).2.val) = (1180209648, 441139635) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1180209648, 441139635⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_15]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 208) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[16]!).2.val) = (338018326, 944583937) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨338018326, 944583937⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_16]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 209) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[17]!).2.val) = (1306248760, 633800785) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1306248760, 633800785⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_17]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 210) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[18]!).2.val) = (2075561284, 1405804402) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2075561284, 1405804402⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_18]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 211) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[19]!).2.val) = (581907879, 73327176) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨581907879, 73327176⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_19]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 212) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[20]!).2.val) = (2049933380, 1834113202) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2049933380, 1834113202⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_20]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 213) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[21]!).2.val) = (1783858788, 875557115) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1783858788, 875557115⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_21]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 214) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[22]!).2.val) = (1718311009, 1065402188) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1718311009, 1065402188⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_22]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 215) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[23]!).2.val) = (1306014716, 1275597287) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1306014716, 1275597287⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_23]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 216) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[24]!).2.val) = (1212070390, 338345678) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1212070390, 338345678⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_24]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 217) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[25]!).2.val) = (1460417120, 797602420) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1460417120, 797602420⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_25]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 218) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[26]!).2.val) = (1852933947, 203671172) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1852933947, 203671172⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_26]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 219) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[27]!).2.val) = (1545193553, 364584318) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1545193553, 364584318⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_27]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 220) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[28]!).2.val) = (1776630073, 603111274) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1776630073, 603111274⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_28]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 221) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[29]!).2.val) = (1049445738, 292144592) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1049445738, 292144592⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_29]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 222) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[30]!).2.val) = (954301220, 1901175687) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨954301220, 1901175687⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_30]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 223) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[31]!).2.val) = (923367882, 1744922936) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨923367882, 1744922936⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk06Certificate.entry_31]
  exact R17TableBChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB06ChunkPower
