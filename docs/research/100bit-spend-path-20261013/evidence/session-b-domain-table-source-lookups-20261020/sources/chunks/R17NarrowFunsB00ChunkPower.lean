import AspisR1QueryGeometryActual.Funs
import R17TableBChunk00Certificate

set_option autoImplicit false

namespace R17NarrowFunsB00ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 0) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[0]!).2.val) = (1, 0) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1, 0⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_00]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 1) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[1]!).2.val) = (996212859, 1140996376) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨996212859, 1140996376⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_01]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 2) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[2]!).2.val) = (2015554631, 1088093947) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2015554631, 1088093947⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_02]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 3) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[3]!).2.val) = (816867225, 1001272228) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨816867225, 1001272228⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_03]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 4) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[4]!).2.val) = (1420207432, 2023238517) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1420207432, 2023238517⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_04]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 5) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[5]!).2.val) = (816861480, 962195439) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨816861480, 962195439⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_05]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 6) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[6]!).2.val) = (1720479643, 177413607) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1720479643, 177413607⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_06]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 7) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[7]!).2.val) = (451378731, 1322552846) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨451378731, 1322552846⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_07]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 8) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[8]!).2.val) = (1330239767, 1446369578) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1330239767, 1446369578⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_08]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 9) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[9]!).2.val) = (829529542, 1666749290) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨829529542, 1666749290⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_09]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 10) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[10]!).2.val) = (1801405099, 774845311) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1801405099, 774845311⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_10]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 11) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[11]!).2.val) = (1643336673, 2137148295) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1643336673, 2137148295⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_11]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 12) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[12]!).2.val) = (113986326, 1659849761) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨113986326, 1659849761⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_12]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 13) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[13]!).2.val) = (754227675, 49211602) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨754227675, 49211602⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_13]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 14) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[14]!).2.val) = (1719877370, 1305056920) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1719877370, 1305056920⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_14]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 15) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[15]!).2.val) = (124061924, 222841901) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨124061924, 222841901⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_15]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 16) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[16]!).2.val) = (1543902459, 1632329423) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1543902459, 1632329423⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_16]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 17) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[17]!).2.val) = (1497033183, 266384758) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1497033183, 266384758⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_17]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 18) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[18]!).2.val) = (238192698, 21195821) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨238192698, 21195821⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_18]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 19) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[19]!).2.val) = (1718190259, 219728259) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1718190259, 219728259⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_19]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 20) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[20]!).2.val) = (837291277, 535367851) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨837291277, 535367851⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_20]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 21) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[21]!).2.val) = (28838794, 517661087) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨28838794, 517661087⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_21]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 22) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[22]!).2.val) = (1008640538, 1400738499) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1008640538, 1400738499⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_22]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 23) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[23]!).2.val) = (18889267, 303036586) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨18889267, 303036586⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_23]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 24) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[24]!).2.val) = (1338697498, 1881711368) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1338697498, 1881711368⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_24]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 25) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[25]!).2.val) = (1486319117, 1051308334) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1486319117, 1051308334⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_25]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 26) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[26]!).2.val) = (57413392, 1672717428) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨57413392, 1672717428⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_26]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 27) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[27]!).2.val) = (1698380290, 1660014787) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1698380290, 1660014787⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_27]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 28) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[28]!).2.val) = (1128628559, 487113817) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1128628559, 487113817⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_28]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 29) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[29]!).2.val) = (1021297342, 1410478134) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1021297342, 1410478134⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_29]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 30) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[30]!).2.val) = (36983955, 1951442989) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨36983955, 1951442989⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_30]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 31) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[31]!).2.val) = (498386322, 1121034294) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨498386322, 1121034294⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk00Certificate.entry_31]
  exact R17TableBChunk00Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB00ChunkPower
