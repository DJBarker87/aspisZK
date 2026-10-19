import AspisR1QueryGeometryActual.Funs
import R17TableBChunk10Certificate

set_option autoImplicit false

namespace R17NarrowFunsB10ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 320) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[0]!).2.val) = (433600440, 167145119) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨433600440, 167145119⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_00]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 321) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[1]!).2.val) = (257107986, 1260243949) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨257107986, 1260243949⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_01]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 322) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[2]!).2.val) = (2117360294, 299533990) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2117360294, 299533990⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_02]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 323) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[3]!).2.val) = (1968789303, 1889430098) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1968789303, 1889430098⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_03]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 324) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[4]!).2.val) = (18918067, 521344418) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨18918067, 521344418⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_04]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 325) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[5]!).2.val) = (212412059, 1208547549) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨212412059, 1208547549⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_05]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 326) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[6]!).2.val) = (526492512, 1146089824) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨526492512, 1146089824⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_06]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 327) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[7]!).2.val) = (1854906262, 225292938) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1854906262, 225292938⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_07]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 328) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[8]!).2.val) = (2001642678, 1520422911) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2001642678, 1520422911⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_08]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 329) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[9]!).2.val) = (1151864086, 1548621786) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1151864086, 1548621786⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_09]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 330) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[10]!).2.val) = (1051514954, 1945490652) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1051514954, 1945490652⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_10]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 331) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[11]!).2.val) = (1231259954, 511844620) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1231259954, 511844620⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_11]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 332) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[12]!).2.val) = (1936661821, 241049853) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1936661821, 241049853⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_12]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 333) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[13]!).2.val) = (54857805, 2021489568) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨54857805, 2021489568⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_13]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 334) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[14]!).2.val) = (2138570352, 385731389) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨2138570352, 385731389⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_14]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 335) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[15]!).2.val) = (830229400, 1396231886) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨830229400, 1396231886⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_15]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 336) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[16]!).2.val) = (36975016, 821963373) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨36975016, 821963373⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_16]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 337) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[17]!).2.val) = (110720662, 731152038) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨110720662, 731152038⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_17]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 338) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[18]!).2.val) = (1672578949, 179250121) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1672578949, 179250121⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_18]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 339) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[19]!).2.val) = (1682843627, 18309514) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1682843627, 18309514⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_19]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 340) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[20]!).2.val) = (183117139, 65944434) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨183117139, 65944434⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_20]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 341) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[21]!).2.val) = (1584827345, 909175004) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1584827345, 909175004⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_21]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 342) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[22]!).2.val) = (1845239625, 562344050) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1845239625, 562344050⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_22]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 343) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[23]!).2.val) = (1315215493, 454778943) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1315215493, 454778943⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_23]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 344) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[24]!).2.val) = (1876139646, 119923533) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1876139646, 119923533⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_24]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 345) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[25]!).2.val) = (750500769, 1547263668) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨750500769, 1547263668⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_25]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 346) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[26]!).2.val) = (849384769, 61803180) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨849384769, 61803180⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_26]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 347) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[27]!).2.val) = (1513012924, 2142060978) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1513012924, 2142060978⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_27]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 348) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[28]!).2.val) = (174156438, 1448257952) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨174156438, 1448257952⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_28]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 349) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[29]!).2.val) = (1976764966, 602953694) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1976764966, 602953694⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_29]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 350) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[30]!).2.val) = (1805314849, 466904232) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1805314849, 466904232⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_30]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk10Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 351) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[31]!).2.val) = (963560469, 803989913) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨963560469, 803989913⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk10Certificate.entry_31]
  exact R17TableBChunk10Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB10ChunkPower
