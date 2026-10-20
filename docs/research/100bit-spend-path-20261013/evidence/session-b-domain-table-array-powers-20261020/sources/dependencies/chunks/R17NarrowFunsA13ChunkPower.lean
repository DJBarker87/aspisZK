import AspisR1QueryGeometryActual.Funs
import R17TableAChunk13Certificate

set_option autoImplicit false

namespace R17NarrowFunsA13ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 416) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[0]!).2.val) = (1952803077, 464954162) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1952803077, 464954162⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_00]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 417) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[1]!).2.val) = (464954162, 194680570) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨464954162, 194680570⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_01]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 418) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[2]!).2.val) = (102502428, 487991121) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨102502428, 487991121⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_02]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 419) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[3]!).2.val) = (487991121, 2044981219) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨487991121, 2044981219⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_03]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 420) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[4]!).2.val) = (286638124, 1789802823) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨286638124, 1789802823⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_04]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 421) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[5]!).2.val) = (1789802823, 1860845523) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1789802823, 1860845523⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_05]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 422) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[6]!).2.val) = (2092563395, 1015929240) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2092563395, 1015929240⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_06]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 423) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[7]!).2.val) = (1015929240, 54920252) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1015929240, 54920252⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_07]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 424) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[8]!).2.val) = (324159263, 1533483219) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨324159263, 1533483219⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_08]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 425) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[9]!).2.val) = (1533483219, 1823324384) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1533483219, 1823324384⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_09]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 426) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[10]!).2.val) = (804875961, 1759135764) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨804875961, 1759135764⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_10]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 427) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[11]!).2.val) = (1759135764, 1342607686) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1759135764, 1342607686⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_11]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 428) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[12]!).2.val) = (706014569, 1757890570) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨706014569, 1757890570⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_12]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 429) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[13]!).2.val) = (1757890570, 1441469078) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1757890570, 1441469078⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_13]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 430) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[14]!).2.val) = (448402140, 760266418) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨448402140, 760266418⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_14]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 431) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[15]!).2.val) = (760266418, 1699081507) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨760266418, 1699081507⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_15]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 432) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[16]!).2.val) = (375974868, 1233265083) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨375974868, 1233265083⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_16]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 433) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[17]!).2.val) = (1233265083, 1771508779) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1233265083, 1771508779⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_17]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 434) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[18]!).2.val) = (113762283, 452178713) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨113762283, 452178713⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_18]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 435) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[19]!).2.val) = (452178713, 2033721364) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨452178713, 2033721364⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_19]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 436) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[20]!).2.val) = (931200852, 642566420) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨931200852, 642566420⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_20]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 437) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[21]!).2.val) = (642566420, 1216282795) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨642566420, 1216282795⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_21]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 438) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[22]!).2.val) = (1681153485, 1692397259) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1681153485, 1692397259⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_22]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 439) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[23]!).2.val) = (1692397259, 466330162) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1692397259, 466330162⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_23]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 440) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[24]!).2.val) = (285193818, 765163688) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨285193818, 765163688⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_24]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 441) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[25]!).2.val) = (765163688, 1862289829) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨765163688, 1862289829⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_25]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 442) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[26]!).2.val) = (394346139, 1629953179) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨394346139, 1629953179⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_26]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 443) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[27]!).2.val) = (1629953179, 1753137508) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1629953179, 1753137508⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_27]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 444) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[28]!).2.val) = (1937755996, 1620967529) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1937755996, 1620967529⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_28]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 445) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[29]!).2.val) = (1620967529, 209727651) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1620967529, 209727651⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_29]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 446) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[30]!).2.val) = (1742951453, 411462942) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1742951453, 411462942⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_30]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk13Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 447) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[31]!).2.val) = (411462942, 404532194) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨411462942, 404532194⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk13Certificate.entry_31]
  exact R17TableAChunk13Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsA13ChunkPower
