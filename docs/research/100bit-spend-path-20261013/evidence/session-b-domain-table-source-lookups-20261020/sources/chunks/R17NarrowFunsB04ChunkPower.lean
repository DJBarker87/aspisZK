import AspisR1QueryGeometryActual.Funs
import R17TableBChunk04Certificate

set_option autoImplicit false

namespace R17NarrowFunsB04ChunkPower

theorem cell_00_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[0]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 128) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[0]!).2.val) = (1799120754, 343598868) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[0]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[0]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1799120754, 343598868⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_00]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_00_circle_power

theorem cell_01_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[1]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 129) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[1]!).2.val) = (1039404017, 1538341569) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[1]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[1]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1039404017, 1538341569⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_01]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_01_circle_power

theorem cell_02_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[2]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 130) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[2]!).2.val) = (666420564, 2135132831) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[2]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[2]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨666420564, 2135132831⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_02]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_02_circle_power

theorem cell_03_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[3]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 131) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[3]!).2.val) = (1006212893, 1489058627) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[3]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[3]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1006212893, 1489058627⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_03]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_03_circle_power

theorem cell_04_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[4]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 132) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[4]!).2.val) = (844712212, 1454882131) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[4]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[4]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨844712212, 1454882131⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_04]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_04_circle_power

theorem cell_05_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[5]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 133) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[5]!).2.val) = (1438323515, 1182923843) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[5]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[5]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1438323515, 1182923843⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_05]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_05_circle_power

theorem cell_06_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[6]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 134) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[6]!).2.val) = (292417279, 377436135) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[6]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[6]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨292417279, 377436135⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_06]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_06_circle_power

theorem cell_07_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[7]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 135) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[7]!).2.val) = (1952780205, 81555357) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[7]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[7]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1952780205, 81555357⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_07]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_07_circle_power

theorem cell_08_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[8]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 136) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[8]!).2.val) = (521340221, 1824173925) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[8]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[8]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨521340221, 1824173925⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_08]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_08_circle_power

theorem cell_09_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[9]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 137) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[9]!).2.val) = (1485690416, 559378410) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[9]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[9]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1485690416, 559378410⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_09]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_09_circle_power

theorem cell_10_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[10]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 138) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[10]!).2.val) = (1714778873, 1735902582) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[10]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[10]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1714778873, 1735902582⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_10]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_10_circle_power

theorem cell_11_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[11]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 139) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[11]!).2.val) = (1180311432, 639492535) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[11]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[11]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1180311432, 639492535⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_11]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_11_circle_power

theorem cell_12_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[12]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 140) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[12]!).2.val) = (245650224, 1174726897) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[12]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[12]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨245650224, 1174726897⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_12]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_12_circle_power

theorem cell_13_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[13]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 141) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[13]!).2.val) = (25525334, 2000505072) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[13]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[13]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨25525334, 2000505072⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_13]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_13_circle_power

theorem cell_14_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[14]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 142) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[14]!).2.val) = (1606261854, 1606869623) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[14]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[14]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1606261854, 1606869623⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_14]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_14_circle_power

theorem cell_15_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[15]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 143) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[15]!).2.val) = (1061095678, 38145073) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[15]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[15]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1061095678, 38145073⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_15]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_15_circle_power

theorem cell_16_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[16]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 144) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[16]!).2.val) = (124482577, 226221110) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[16]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[16]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨124482577, 226221110⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_16]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_16_circle_power

theorem cell_17_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[17]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 145) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[17]!).2.val) = (172504864, 1916272282) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[17]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[17]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨172504864, 1916272282⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_17]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_17_circle_power

theorem cell_18_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[18]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 146) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[18]!).2.val) = (1564877543, 99597748) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[18]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[18]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1564877543, 99597748⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_18]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_18_circle_power

theorem cell_19_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[19]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 147) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[19]!).2.val) = (876115079, 1775942790) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[19]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[19]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨876115079, 1775942790⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_19]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_19_circle_power

theorem cell_20_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[20]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 148) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[20]!).2.val) = (530115096, 90442098) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[20]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[20]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨530115096, 90442098⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_20]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_20_circle_power

theorem cell_21_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[21]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 149) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[21]!).2.val) = (1392272834, 993120013) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[21]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[21]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1392272834, 993120013⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_21]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_21_circle_power

theorem cell_22_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[22]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 150) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[22]!).2.val) = (399207028, 155898355) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[22]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[22]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨399207028, 155898355⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_22]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_22_circle_power

theorem cell_23_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[23]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 151) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[23]!).2.val) = (1327578729, 1084731515) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[23]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[23]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1327578729, 1084731515⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_23]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_23_circle_power

theorem cell_24_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[24]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 152) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[24]!).2.val) = (607954189, 1091734815) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[24]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[24]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨607954189, 1091734815⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_24]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_24_circle_power

theorem cell_25_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[25]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 153) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[25]!).2.val) = (1323669817, 933421634) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[25]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[25]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1323669817, 933421634⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_25]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_25_circle_power

theorem cell_26_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[26]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 154) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[26]!).2.val) = (1478673705, 1008068784) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[26]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[26]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1478673705, 1008068784⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_26]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_26_circle_power

theorem cell_27_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[27]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 155) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[27]!).2.val) = (1962335487, 1399131158) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[27]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[27]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1962335487, 1399131158⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_27]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_27_circle_power

theorem cell_28_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[28]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 156) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[28]!).2.val) = (1055871441, 345775465) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[28]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[28]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1055871441, 345775465⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_28]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_28_circle_power

theorem cell_29_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[29]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 157) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[29]!).2.val) = (711647904, 1091839298) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[29]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[29]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨711647904, 1091839298⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_29]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_29_circle_power

theorem cell_30_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[30]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 158) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[30]!).2.val) = (881168337, 157473534) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[30]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[30]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨881168337, 157473534⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_30]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_30_circle_power

theorem cell_31_circle_power :
    R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[31]!).2.val⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode (R17TableBChunk04Certificate.toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 159) := by
  have hcell : ((AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[31]!).2.val) = (1723511612, 1949091952) := rfl
  have hC : (⟨(AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[31]!).1.val, (AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[31]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨1723511612, 1949091952⟩ := by
    have h₁ := congrArg Prod.fst hcell
    have h₂ := congrArg Prod.snd hcell
    cases h₁
    cases h₂
    rfl
  rw [hC]
  rw [← R17TableBChunk04Certificate.entry_31]
  exact R17TableBChunk04Certificate.fastPow_decode_zPow _

#print axioms cell_31_circle_power

end R17NarrowFunsB04ChunkPower
