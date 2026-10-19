import AspisR1QueryGeometryActual.Funs
import R17TableAChunk15Certificate

set_option autoImplicit false

namespace R17NarrowFunsA15ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 480) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[0]!).2.val) = (1529521733, 1200601350) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1529521733, 1200601350⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_00]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 481) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[1]!).2.val) = (1200601350, 617961914) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1200601350, 617961914⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_01]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 482) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[2]!).2.val) = (799417018, 157314149) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨799417018, 157314149⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_02]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 483) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[3]!).2.val) = (157314149, 1348066629) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨157314149, 1348066629⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_03]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 484) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[4]!).2.val) = (1811854824, 734127761) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1811854824, 734127761⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_04]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 485) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[5]!).2.val) = (734127761, 335628823) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨734127761, 335628823⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_05]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 486) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[6]!).2.val) = (1312626624, 408174531) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1312626624, 408174531⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_06]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 487) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[7]!).2.val) = (408174531, 834857023) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨408174531, 834857023⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_07]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 488) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[8]!).2.val) = (388664435, 1700426073) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨388664435, 1700426073⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_08]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 489) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[9]!).2.val) = (1700426073, 1758819212) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1700426073, 1758819212⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_09]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 490) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[10]!).2.val) = (2129034372, 1920159279) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2129034372, 1920159279⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_10]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 491) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[11]!).2.val) = (1920159279, 18449275) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1920159279, 18449275⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_11]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 492) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[12]!).2.val) = (1031337775, 1391460640) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1031337775, 1391460640⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_12]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 493) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[13]!).2.val) = (1391460640, 1116145872) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1391460640, 1116145872⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_13]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 494) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[14]!).2.val) = (2083000424, 83400055) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2083000424, 83400055⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_14]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 495) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[15]!).2.val) = (83400055, 64483223) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨83400055, 64483223⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_15]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 496) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[16]!).2.val) = (1755212887, 1545248590) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1755212887, 1545248590⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_16]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 497) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[17]!).2.val) = (1545248590, 392270760) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1545248590, 392270760⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_17]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 498) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[18]!).2.val) = (97731769, 427520892) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨97731769, 427520892⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_18]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 499) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[19]!).2.val) = (427520892, 2049751878) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨427520892, 2049751878⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_19]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 500) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[20]!).2.val) = (1461518819, 1258709018) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1461518819, 1258709018⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_20]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 501) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[21]!).2.val) = (1258709018, 685964828) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1258709018, 685964828⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_21]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 502) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[22]!).2.val) = (822026787, 790328297) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨822026787, 790328297⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_22]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 503) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[23]!).2.val) = (790328297, 1325456860) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨790328297, 1325456860⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_23]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 504) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[24]!).2.val) = (1887931203, 983768063) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1887931203, 983768063⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_24]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 505) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[25]!).2.val) = (983768063, 259552444) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨983768063, 259552444⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_25]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 506) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[26]!).2.val) = (1403104042, 1214106139) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1403104042, 1214106139⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_26]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 507) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[27]!).2.val) = (1214106139, 744379605) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1214106139, 744379605⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_27]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 508) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[28]!).2.val) = (162197904, 1576977305) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨162197904, 1576977305⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_28]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 509) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[29]!).2.val) = (1576977305, 1985285743) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1576977305, 1985285743⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_29]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 510) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[30]!).2.val) = (1519708073, 1761924179) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1519708073, 1761924179⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_30]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 511) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[31]!).2.val) = (1761924179, 627775574) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1761924179, 627775574⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk15Certificate.entry_31]
  exact R17TableAChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsA15ChunkPower
