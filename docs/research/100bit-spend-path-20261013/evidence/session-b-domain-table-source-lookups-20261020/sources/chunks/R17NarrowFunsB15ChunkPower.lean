import AspisR1QueryGeometryActual.Funs
import R17TableBChunk15Certificate

set_option autoImplicit false

namespace R17NarrowFunsB15ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 480) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[0]!).2.val) = (1168068815, 1631133982) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1168068815, 1631133982⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_00]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 481) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[1]!).2.val) = (598225672, 477392696) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨598225672, 477392696⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_01]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 482) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[2]!).2.val) = (1272345615, 2072662117) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1272345615, 2072662117⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_02]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 483) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[3]!).2.val) = (1788571406, 979662875) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1788571406, 979662875⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_03]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 484) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[4]!).2.val) = (655623719, 353143806) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨655623719, 353143806⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_04]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 485) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[5]!).2.val) = (1258493728, 1482265298) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1258493728, 1482265298⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_05]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 486) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[6]!).2.val) = (854296756, 1657148963) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨854296756, 1657148963⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_06]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 487) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[7]!).2.val) = (1287455995, 1262269285) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1287455995, 1262269285⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_07]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 488) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[8]!).2.val) = (1389630114, 73256692) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1389630114, 73256692⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_08]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 489) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[9]!).2.val) = (463066423, 383444756) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨463066423, 383444756⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_09]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 490) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[10]!).2.val) = (401706099, 967129345) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨401706099, 967129345⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_10]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 491) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[11]!).2.val) = (1055629173, 1510653447) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1055629173, 1510653447⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_11]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 492) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[12]!).2.val) = (1775957340, 1042791219) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1775957340, 1042791219⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_12]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 493) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[13]!).2.val) = (1767305484, 1767768510) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1767305484, 1767768510⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_13]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 494) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[14]!).2.val) = (702523908, 198087577) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨702523908, 198087577⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_14]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 495) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[15]!).2.val) = (498379185, 365852161) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨498379185, 365852161⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_15]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 496) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[16]!).2.val) = (1029759507, 977441374) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1029759507, 977441374⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_16]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 497) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[17]!).2.val) = (531874659, 2093948690) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨531874659, 2093948690⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_17]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 498) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[18]!).2.val) = (274337143, 1881376116) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨274337143, 1881376116⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_18]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 499) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[19]!).2.val) = (1734948438, 924408729) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1734948438, 924408729⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_19]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 500) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[20]!).2.val) = (875099799, 1659345298) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨875099799, 1659345298⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_20]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 501) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[21]!).2.val) = (1568619121, 824042977) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1568619121, 824042977⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_21]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 502) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[22]!).2.val) = (936298450, 1105042578) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨936298450, 1105042578⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_22]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 503) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[23]!).2.val) = (1577684276, 2022021752) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1577684276, 2022021752⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_23]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 504) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[24]!).2.val) = (404074859, 398369746) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨404074859, 398369746⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_24]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 505) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[25]!).2.val) = (931704942, 1582955093) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨931704942, 1582955093⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_25]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 506) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[26]!).2.val) = (18011247, 565274326) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨18011247, 565274326⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_26]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 507) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[27]!).2.val) = (931164423, 2037669329) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨931164423, 2037669329⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_27]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 508) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[28]!).2.val) = (1309629376, 2080668066) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1309629376, 2080668066⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_28]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 509) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[29]!).2.val) = (1286492231, 1508399759) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1286492231, 1508399759⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_29]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 510) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[30]!).2.val) = (1807661853, 544066780) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1807661853, 544066780⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_30]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk15Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 511) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[31]!).2.val) = (1942053500, 1814876063) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1942053500, 1814876063⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk15Certificate.entry_31]
  exact R17TableBChunk15Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB15ChunkPower
