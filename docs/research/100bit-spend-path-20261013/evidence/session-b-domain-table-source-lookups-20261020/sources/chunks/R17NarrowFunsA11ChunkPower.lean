import AspisR1QueryGeometryActual.Funs
import R17TableAChunk11Certificate

set_option autoImplicit false

namespace R17NarrowFunsA11ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 352) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[0]!).2.val) = (635778846, 1298887220) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨635778846, 1298887220⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_00]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 353) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[1]!).2.val) = (1298887220, 1511704801) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1298887220, 1511704801⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_01]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 354) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[2]!).2.val) = (1420391248, 495658886) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1420391248, 495658886⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_02]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 355) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[3]!).2.val) = (495658886, 727092399) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨495658886, 727092399⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_03]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 356) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[4]!).2.val) = (1273099376, 2109025845) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1273099376, 2109025845⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_04]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 357) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[5]!).2.val) = (2109025845, 874384271) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2109025845, 874384271⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_05]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 358) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[6]!).2.val) = (290670999, 484618707) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨290670999, 484618707⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_06]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 359) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[7]!).2.val) = (484618707, 1856812648) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨484618707, 1856812648⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_07]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 360) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[8]!).2.val) = (1953093309, 1399852939) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1953093309, 1399852939⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_08]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 361) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[9]!).2.val) = (1399852939, 194390338) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1399852939, 194390338⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_09]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 362) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[10]!).2.val) = (1931790297, 476503814) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1931790297, 476503814⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_10]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 363) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[11]!).2.val) = (476503814, 215693350) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨476503814, 215693350⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_11]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 364) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[12]!).2.val) = (1168611337, 1316554005) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1168611337, 1316554005⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_12]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 365) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[13]!).2.val) = (1316554005, 978872310) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1316554005, 978872310⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_13]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 366) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[14]!).2.val) = (1318032416, 914753745) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1318032416, 914753745⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_14]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 367) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[15]!).2.val) = (914753745, 829451231) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨914753745, 829451231⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_15]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 368) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[16]!).2.val) = (1016770609, 602494260) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1016770609, 602494260⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_16]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 369) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[17]!).2.val) = (602494260, 1130713038) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨602494260, 1130713038⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_17]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 370) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[18]!).2.val) = (45277316, 1384212302) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨45277316, 1384212302⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_18]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 371) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[19]!).2.val) = (1384212302, 2102206331) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1384212302, 2102206331⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_19]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 372) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[20]!).2.val) = (298013744, 1631477536) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨298013744, 1631477536⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_20]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 373) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[21]!).2.val) = (1631477536, 1849469903) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1631477536, 1849469903⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_21]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 374) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[22]!).2.val) = (1504211713, 91770747) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1504211713, 91770747⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_22]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 375) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[23]!).2.val) = (91770747, 643271934) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨91770747, 643271934⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_23]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 376) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[24]!).2.val) = (321646901, 781973549) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨321646901, 781973549⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_24]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 377) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[25]!).2.val) = (781973549, 1825836746) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨781973549, 1825836746⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_25]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 378) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[26]!).2.val) = (1957773767, 58465136) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1957773767, 58465136⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_26]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 379) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[27]!).2.val) = (58465136, 189709880) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨58465136, 189709880⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_27]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 380) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[28]!).2.val) = (838659345, 1494392856) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨838659345, 1494392856⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_28]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 381) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[29]!).2.val) = (1494392856, 1308824302) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1494392856, 1308824302⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_29]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 382) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[30]!).2.val) = (1184172815, 1501800213) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1184172815, 1501800213⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_30]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk11Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 383) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[31]!).2.val) = (1501800213, 963310832) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1501800213, 963310832⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk11Certificate.entry_31]
  exact R17TableAChunk11Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsA11ChunkPower
