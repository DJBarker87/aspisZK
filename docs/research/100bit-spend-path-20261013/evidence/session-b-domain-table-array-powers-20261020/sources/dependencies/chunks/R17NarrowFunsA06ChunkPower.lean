import AspisR1QueryGeometryActual.Funs
import R17TableAChunk06Certificate

set_option autoImplicit false

namespace R17NarrowFunsA06ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 192) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[0]!).2.val) = (2123635407, 1081507110) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2123635407, 1081507110⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_00]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 193) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[1]!).2.val) = (1081507110, 23848240) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1081507110, 23848240⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_01]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 194) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[2]!).2.val) = (1274756874, 824918498) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1274756874, 824918498⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_02]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 195) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[3]!).2.val) = (824918498, 872726773) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨824918498, 872726773⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_03]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 196) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[4]!).2.val) = (75612694, 638305945) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨75612694, 638305945⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_04]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 197) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[5]!).2.val) = (638305945, 2071870953) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨638305945, 2071870953⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_05]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 198) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[6]!).2.val) = (1146595981, 37855626) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1146595981, 37855626⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_06]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 199) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[7]!).2.val) = (37855626, 1000887666) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨37855626, 1000887666⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_07]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 200) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[8]!).2.val) = (1128749075, 1106851245) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1128749075, 1106851245⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_08]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 201) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[9]!).2.val) = (1106851245, 1018734572) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1106851245, 1018734572⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_09]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 202) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[10]!).2.val) = (1189119296, 1858928305) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1189119296, 1858928305⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_10]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 203) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[11]!).2.val) = (1858928305, 958364351) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1858928305, 958364351⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_11]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 204) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[12]!).2.val) = (1936509027, 329657887) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1936509027, 329657887⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_12]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 205) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[13]!).2.val) = (329657887, 210974620) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨329657887, 210974620⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_13]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 206) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[14]!).2.val) = (2067891986, 853385273) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2067891986, 853385273⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_14]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 207) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[15]!).2.val) = (853385273, 79591661) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨853385273, 79591661⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_15]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 208) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[16]!).2.val) = (242763393, 80138650) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨242763393, 80138650⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_16]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 209) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[17]!).2.val) = (80138650, 1904720254) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨80138650, 1904720254⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_17]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 210) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[18]!).2.val) = (202216255, 1166833230) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨202216255, 1166833230⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_18]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 211) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[19]!).2.val) = (1166833230, 1945267392) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1166833230, 1945267392⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_19]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 212) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[20]!).2.val) = (1704605091, 1002003657) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1704605091, 1002003657⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_20]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 213) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[21]!).2.val) = (1002003657, 442878556) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1002003657, 442878556⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_21]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 214) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[22]!).2.val) = (1228317011, 328390175) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1228317011, 328390175⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_22]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 215) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[23]!).2.val) = (328390175, 919166636) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨328390175, 919166636⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_23]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 216) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[24]!).2.val) = (1870718732, 902417887) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1870718732, 902417887⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_24]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 217) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[25]!).2.val) = (902417887, 276764915) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨902417887, 276764915⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_25]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 218) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[26]!).2.val) = (1517692234, 1936279112) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1517692234, 1936279112⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_26]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 219) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[27]!).2.val) = (1936279112, 629791413) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1936279112, 629791413⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_27]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 220) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[28]!).2.val) = (1050410086, 1073301032) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1050410086, 1073301032⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_28]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 221) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[29]!).2.val) = (1073301032, 1097073561) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1073301032, 1097073561⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_29]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 222) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[30]!).2.val) = (558333589, 618725725) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨558333589, 618725725⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_30]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableAChunk06Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 223) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[31]!).2.val) = (618725725, 1589150058) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨618725725, 1589150058⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableAChunk06Certificate.entry_31]
  exact R17TableAChunk06Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsA06ChunkPower
