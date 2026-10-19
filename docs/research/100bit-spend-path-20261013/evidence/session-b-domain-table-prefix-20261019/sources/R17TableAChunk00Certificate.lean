import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk00Certificate
open R17MinimalReverseBits
open R17TableExponentDomainBridge
open R17TableBasePowerProbe

def toNatC (x : R17TableBasePowerProbe.C) :
    R17TableBasePowerBridge.NatC := ⟨x.re, x.im⟩

theorem toNatC_cmul (x y : R17TableBasePowerProbe.C) :
    toNatC (R17TableBasePowerProbe.cmul x y) =
      R17TableBasePowerBridge.natMul (toNatC x) (toNatC y) := rfl

theorem fastPow_succ (x : R17TableBasePowerProbe.C) (k : Nat) :
    R17TableBasePowerProbe.fastPow x (k + 1) =
      let y := R17TableBasePowerProbe.fastPow x ((k + 1) / 2)
      if (k + 1) % 2 == 0 then R17TableBasePowerProbe.cmul y y
      else R17TableBasePowerProbe.cmul (R17TableBasePowerProbe.cmul y y) x := by
  simp [R17TableBasePowerProbe.fastPow]

theorem fastPow_toNatPow (x : R17TableBasePowerProbe.C) (n : Nat) :
    toNatC (R17TableBasePowerProbe.fastPow x n) =
      R17TableBasePowerBridge.natPow (toNatC x) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [R17TableBasePowerProbe.fastPow, R17TableBasePowerBridge.natPow,
        R17TableBasePowerProbe.cone, R17TableBasePowerBridge.oneN, toNatC]
    | succ k =>
      have hm : (k + 1) / 2 < k + 1 := by omega
      have him := ih ((k + 1) / 2) hm
      simp only [R17TableBasePowerProbe.fastPow, R17TableBasePowerBridge.natPow]
      by_cases hparity : (k + 1) % 2 == 0
      · simp only [toNatC_cmul, if_pos hparity, him]
      · simp only [toNatC_cmul, if_neg hparity, him]

theorem fastPow_decode_zPow (n : Nat) :
    R17TableBasePowerBridge.decode
        (toNatC (R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen n)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen)) n := by
  rw [fastPow_toNatPow]
  exact R17TableBasePowerBridge.natPow_decode_zPow (toNatC R17TableBasePowerProbe.gen) n

theorem power_0 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 0 = ⟨1, 0⟩ := by simp [R17TableBasePowerProbe.fastPow, R17TableBasePowerProbe.cone]

theorem power_1 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1 = ⟨2, 1268011823⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_0]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2 = ⟨7, 777079998⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3 = ⟨26, 1840308169⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4 = ⟨97, 141701737⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5 = ⟨362, 873982426⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6 = ⟨1351, 1206744320⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7 = ⟨5042, 1805511207⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8 = ⟨18817, 1720333214⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9 = ⟨70226, 780854355⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10 = ⟨262087, 1403084206⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11 = ⟨978122, 536515175⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12 = ⟨3650401, 742976494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13 = ⟨13623482, 287907154⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14 = ⟨50843527, 408652122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15 = ⟨189750626, 1346701334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16 = ⟨708158977, 683185920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17 = ⟨495401635, 1386042346⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18 = ⟨1273447563, 566016170⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19 = ⟨303421323, 878022334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20 = ⟨2087721376, 798589519⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21 = ⟨1605013240, 168852095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22 = ⟨37364290, 2024302508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23 = ⟨691927567, 1485906996⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24 = ⟨582862331, 1771841829⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25 = ⟨1639521757, 1306493026⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26 = ⟨1680257403, 1306646628⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27 = ⟨786540561, 1772609839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28 = ⟨1465904841, 1488825434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29 = ⟨782111509, 2035208250⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30 = ⟨1662541195, 209556625⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31 = ⟨1573085977, 950501897⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32 = ⟨334835419, 1444967316⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34 = ⟨877671024, 692632976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36 = ⟨1215140682, 1809443407⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38 = ⟨1101912995, 1017254605⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40 = ⟨1326739366, 1694702828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42 = ⟨292568953, 1233748517⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44 = ⟨621742329, 545390881⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46 = ⟨1969372712, 2106756523⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48 = ⟨1179671875, 1031913030⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50 = ⟨1661131656, 1602607662⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52 = ⟨601334839, 2077241415⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54 = ⟨315105149, 1708968384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56 = ⟨1662653600, 373479491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58 = ⟨1487208781, 1372260843⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60 = ⟨1978400158, 1658303135⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62 = ⟨440589667, 369146577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64 = ⟨2042371533, 1362265296⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_68 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 68 = ⟨1252169843, 628159355⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72 = ⟨360409545, 241565342⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76 = ⟨2095288830, 1138360406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_80 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 80 = ⟨251214192, 1557021428⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_84 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84 = ⟨1543107831, 276086046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88 = ⟨611478089, 464063968⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92 = ⟨1119524497, 1705494219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_96 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96 = ⟨1827909629, 1836816527⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_100 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100 = ⟨1307625421, 302110264⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104 = ⟨595835346, 937999867⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108 = ⟨467798412, 1281237586⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112 = ⟨2110227055, 661472412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_116 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116 = ⟨894357328, 342875169⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120 = ⟨1743886464, 1431800964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124 = ⟨264684109, 401121384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128 = ⟨212706801, 1223819887⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 136 = ⟨1739793648, 871532832⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 144 = ⟨552528648, 1672522617⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 152 = ⟨186674930, 98941776⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 160 = ⟨352777635, 313115116⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 168 = ⟨502934906, 432562679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 176 = ⟨1326093758, 824702110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 184 = ⟨337081033, 972978617⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 192 = ⟨1343082982, 1656388718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 200 = ⟨2072747763, 552213126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 208 = ⟨1397719779, 1280626794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 216 = ⟨1396449152, 728546296⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 224 = ⟨1497340852, 2054439268⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 232 = ⟨1705761383, 185122675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 240 = ⟨545370846, 562844461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 248 = ⟨1426926249, 1272112238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 256 = ⟨421007138, 256177860⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 272 = ⟨1106204247, 1950210306⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 288 = ⟨1178716014, 1579375203⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 304 = ⟨1931014169, 1213553800⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 320 = ⟨1637047685, 109864373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 336 = ⟨180537201, 1575865056⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 352 = ⟨2122028404, 1461483964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 368 = ⟨2105144309, 259436035⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 384 = ⟨1594705154, 1156423391⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 400 = ⟨1872990432, 1178172302⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 416 = ⟨1719486678, 1121851154⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 432 = ⟨2080418350, 1727780629⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 448 = ⟨1326191972, 1554410474⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 464 = ⟨761225645, 1514363314⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 480 = ⟨300788412, 2003762236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 496 = ⟨496157480, 1934975487⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 512 = ⟨6346213, 905523693⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 544 = ⟨1192151435, 1028938634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 576 = ⟨1603309155, 1317339952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 608 = ⟨112946548, 968926260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 640 = ⟨982766847, 1369509443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 672 = ⟨1863904991, 681598711⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 704 = ⟨1130890301, 1314091057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 736 = ⟨103504458, 1923745518⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 768 = ⟨784830374, 912241638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 800 = ⟨1630963856, 82519081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 832 = ⟨529167155, 49384636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 864 = ⟨1921307644, 464663069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 896 = ⟨1475671350, 739745329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 928 = ⟨192925011, 1863974752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 960 = ⟨418523497, 1921984699⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 992 = ⟨175521256, 1612727439⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1024 = ⟨1022251061, 788094511⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1088 = ⟨1453585800, 1686756607⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1152 = ⟨2144756169, 1973977555⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1216 = ⟨222118537, 1014253609⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1280 = ⟨1774187400, 1713497086⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1344 = ⟨1447121614, 1053732556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1408 = ⟨105012991, 261334420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1472 = ⟨1509980434, 1580004926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1536 = ⟨999230472, 1852479283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1600 = ⟨517742188, 968413651⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1664 = ⟨288424812, 1959942454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1728 = ⟨1136461567, 2028297119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1792 = ⟨344093444, 1723950257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1856 = ⟨2162587, 1662102570⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1920 = ⟨203869561, 313423390⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1984 = ⟨57053772, 179506272⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2048 = ⟨1633461177, 574296567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2176 = ⟨1655011431, 2085598907⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2304 = ⟨505774551, 1187398701⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2432 = ⟨1676081227, 1135991864⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2560 = ⟨1743980363, 345791924⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2688 = ⟨319360190, 618255967⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2816 = ⟨638925477, 1200786367⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2944 = ⟨1091919627, 1535715623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3072 = ⟨2054061671, 949045631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3200 = ⟨1230785717, 932947748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3328 = ⟨1399167609, 1906303117⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3456 = ⟨1696585972, 468920631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3584 = ⟨1309393381, 53742718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3712 = ⟨1273782452, 924138332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3840 = ⟨2080156404, 1988869649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3968 = ⟨1619251001, 830366565⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4096 = ⟨595037635, 2111542451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4352 = ⟨718921583, 1008587178⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4608 = ⟨1781794005, 336873408⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4864 = ⟨1327275430, 1972188598⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5120 = ⟨235158087, 2112924242⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5376 = ⟨967187167, 1461124768⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5632 = ⟨1739299167, 1982296282⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5888 = ⟨1683866914, 365976087⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6144 = ⟨1121167, 714917308⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6400 = ⟨977208331, 1995798003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6656 = ⟨1510720600, 1956487951⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6912 = ⟨900851131, 714016362⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7168 = ⟨1883166840, 347102028⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7424 = ⟨719349967, 2102971509⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7680 = ⟨1699022782, 2146531477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7936 = ⟨162722436, 856104198⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8192 = ⟨1799120754, 343598868⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8704 = ⟨252837685, 2006332926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9216 = ⟨1702571195, 1397706324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9728 = ⟨76857669, 1277280684⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10240 = ⟨1242192167, 1322293366⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10752 = ⟨133802874, 733650364⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11264 = ⟨226985029, 1154128883⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11776 = ⟨1650999925, 82499284⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12288 = ⟨1475016787, 1876816901⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12800 = ⟨670508625, 2057653994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13312 = ⟨721344225, 1097609337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13824 = ⟨2122891308, 1958068349⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14336 = ⟨1731306458, 1551812567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14848 = ⟨520833839, 1618182004⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15360 = ⟨1368263916, 2076980552⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15872 = ⟨1544810668, 1648948073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16384 = ⟨438833264, 1327019128⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17408 = ⟨913684129, 1336358039⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18432 = ⟨1139757936, 161139962⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19456 = ⟨1672882969, 1149947594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20480 = ⟨433600440, 167145119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21504 = ⟨1700714437, 566394792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22528 = ⟨286695904, 1021278776⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23552 = ⟨1609631824, 2034059636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24576 = ⟨503318431, 730224775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25600 = ⟨1627995231, 271303573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26624 = ⟨2056541252, 1900478857⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27648 = ⟨405776385, 918871706⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28672 = ⟨1124768046, 299494314⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29696 = ⟨1800149012, 1373092732⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30720 = ⟨1155186462, 790771269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31744 = ⟨2081374532, 23687746⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32768 = ⟨1389168750, 838891026⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32769 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32769 = ⟨726554457, 1541224488⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34816 = ⟨1765678898, 2028236613⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36864 = ⟨1421883301, 1767600112⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38912 = ⟨1693740220, 848695353⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40960 = ⟨263253631, 1948074535⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43008 = ⟨1503715524, 748528002⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45056 = ⟨1984370174, 548484416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47104 = ⟨496848496, 890027025⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49152 = ⟨377761958, 572545120⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51200 = ⟨687167191, 1193781868⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53248 = ⟨528497962, 2048433423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55296 = ⟨643989886, 49445127⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57344 = ⟨347749121, 1576860820⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59392 = ⟨1076514332, 1068664781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61440 = ⟨1168068815, 1631133982⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63488 = ⟨498226347, 579000983⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65536 = ⟨1543902459, 1632329423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65537 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65537 = ⟨1029291272, 16002006⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65538 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65538 = ⟨425778982, 579162248⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32769]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69632 = ⟨1964662320, 1382435771⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73728 = ⟨124482577, 226221110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77824 = ⟨1214106985, 780900129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_81920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81920 = ⟨1635360495, 1075839836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_86016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86016 = ⟨36975016, 821963373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90112 = ⟨338018326, 944583937⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94208 = ⟨1753543609, 1294275673⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98304 = ⟨13191618, 303576968⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98305 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98305 = ⟨1473257791, 112048678⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102400 = ⟨606906923, 1264738384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106496 = ⟨1488671228, 939868393⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_110592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110592 = ⟨854984042, 63484416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_114688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114688 = ⟨1825664712, 501661179⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_118784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118784 = ⟨845078094, 149898124⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122880 = ⟨1829052821, 673049321⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126976 = ⟨1029759507, 977441374⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_131072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131072 = ⟨1330239767, 1446369578⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_131073 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131073 = ⟨1209582064, 427436204⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_131074 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131074 = ⟨1360604842, 263375238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65537]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_131076 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131076 = ⟨538358845, 93400107⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65538]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_139264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 139264 = ⟨521340221, 1824173925⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_147456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 147456 = ⟨1384581133, 347627210⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_155648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 155648 = ⟨940196297, 1361581394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_163840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 163840 = ⟨296310565, 109983397⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_163841 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 163841 = ⟨1631337032, 1967529067⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_172032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 172032 = ⟨735504938, 198004457⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_180224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 180224 = ⟨324121113, 147452506⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_188416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 188416 = ⟨1213375404, 771547637⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_196608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 196608 = ⟨1338697498, 1881711368⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_196609 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 196609 = ⟨6979670, 933526455⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_196610 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 196610 = ⟨836704829, 1852394452⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98305]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_204800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 204800 = ⟨607954189, 1091734815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_212992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 212992 = ⟨1004021208, 1870425365⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_221184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 221184 = ⟨1212070390, 338345678⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_229376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 229376 = ⟨1577483195, 846841358⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_229377 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 229377 = ⟨1150630206, 1256367499⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_237568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 237568 = ⟨474711937, 1020011657⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_245760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 245760 = ⟨640220223, 1154724018⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_253952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 253952 = ⟨44588143, 2058311453⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_262144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 262144 = ⟨1420207432, 2023238517⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_262145 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 262145 = ⟨23951694, 1526383534⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_262146 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 262146 = ⟨823082991, 1934811972⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131073]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_262148 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 262148 = ⟨1513019854, 1441808974⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131074]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_262152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 262152 = ⟨47868252, 662311976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131076]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_278528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 278528 = ⟨694768587, 1335510377⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_139264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_294912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 294912 = ⟨240698073, 476721530⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_147456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_294913 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 294913 = ⟨232307726, 1664689642⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_147456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_311296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 311296 = ⟨2051626085, 490550043⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_155648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_327680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 327680 = ⟨837291277, 535367851⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_163840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_327681 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 327681 = ⟨686493625, 497256989⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_163840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_327682 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 327682 = ⟨1908683223, 1453660105⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_163841]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_344064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 344064 = ⟨2128165408, 1866558246⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_172032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_360448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 360448 = ⟨1363572456, 1209117074⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_180224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_360449 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 360449 = ⟨878614885, 985520052⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_180224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_376832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 376832 = ⟨1466126871, 410615561⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_188416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_393216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 393216 = ⟨113986326, 1659849761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_196608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_393217 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 393217 = ⟨1702497669, 1296335045⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_196608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_393218 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 393218 = ⟨253553409, 1378006772⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_196609]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_393220 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 393220 = ⟨1288277753, 452375871⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_196610]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_409600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 409600 = ⟨1971845238, 153904061⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_204800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_425984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 425984 = ⟨472230981, 1127178204⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_212992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_425985 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 425985 = ⟨2141769354, 1202090030⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_212992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_442368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 442368 = ⟨1174950059, 1819822737⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_221184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_458752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 458752 = ⟨1128628559, 487113817⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_229376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_458753 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 458753 = ⟨850219834, 723882253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_229376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_458754 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 458754 = ⟨124767130, 260931548⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_229377]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_475136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 475136 = ⟨1461783988, 258760706⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_237568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_491520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 491520 = ⟨389608651, 1555639321⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_245760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_491521 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 491521 = ⟨385008587, 5726938⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_245760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_507904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 507904 = ⟨1581002989, 970103636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_253952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_524289 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 524289 = ⟨1862151862, 263590118⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_262144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_524290 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 524290 = ⟨1138085523, 2113750172⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_262145]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_524292 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 524292 = ⟨1032740809, 587121050⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_262146]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_524296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 524296 = ⟨767666791, 1144240109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_262148]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_524304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 524304 = ⟨406438419, 2049562162⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_262152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_557057 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 557057 = ⟨629014851, 1574772148⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_278528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_589825 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 589825 = ⟨1261348103, 1206040697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_294912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_589826 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 589826 = ⟨512232420, 507999673⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_294913]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_622593 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 622593 = ⟨191029122, 1733018193⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_311296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_655361 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 655361 = ⟨2024847170, 1488671328⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_327680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_655362 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 655362 = ⟨2003016287, 884872707⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_327681]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_655364 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 655364 = ⟨471019155, 875954352⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_327682]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_688129 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 688129 = ⟨466079220, 1868647789⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_344064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_720897 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 720897 = ⟨815564278, 1483048151⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_360448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_720898 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 720898 = ⟨1057360073, 2111991529⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_360449]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_753665 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 753665 = ⟨1442511067, 1323142748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_376832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_786433 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 786433 = ⟨748292175, 474421422⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_393216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_786434 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 786434 = ⟨1272689057, 1720272081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_393217]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_786436 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 786436 = ⟨1064781626, 284075410⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_393218]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_786440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 786440 = ⟨836209336, 1246124758⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_393220]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_819201 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 819201 = ⟨1126390000, 319305279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_409600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_851969 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 851969 = ⟨1116849653, 397472710⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_425984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_851970 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 851970 = ⟨1311274427, 189152341⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_425985]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_884737 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 884737 = ⟨1661214448, 973620778⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_442368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_917505 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 917505 = ⟨1667386924, 1579580509⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_458752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_917506 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 917506 = ⟨654703032, 718297822⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_458753]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_917508 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 917508 = ⟨1003514137, 161178000⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_458754]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_950273 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 950273 = ⟨224798466, 1368479942⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_475136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_983041 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 983041 = ⟨1432430206, 1056028631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_491520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_983042 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 983042 = ⟨1397769575, 125187888⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_491521]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1015809 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1015809 = ⟨817941766, 1567321620⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_507904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1048578 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1048578 = ⟨64586973, 278528542⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_524289]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1048580 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1048580 = ⟨2055488410, 610919565⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_524290]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1048584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1048584 = ⟨484063986, 1413282296⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_524292]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1048592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1048592 = ⟨1311542411, 1744929686⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_524296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1048608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1048608 = ⟨676929663, 2069594996⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_524304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1114114 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1114114 = ⟨1306646683, 1478858384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_557057]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1179650 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1179650 = ⟨2115862824, 908076317⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_589825]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1179652 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1179652 = ⟨875262583, 308900913⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_589826]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1245186 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1245186 = ⟨526258587, 870257257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_622593]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1310722 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1310722 = ⟨527921458, 2075129130⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_655361]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1310724 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1310724 = ⟨131587991, 172324970⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_655362]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1310728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1310728 = ⟨1088888657, 256594036⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_655364]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1376258 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1376258 = ⟨706766508, 894103403⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_688129]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1441794 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1441794 = ⟨952064134, 676267856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_720897]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1441796 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1441796 = ⟨1837251966, 828603794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_720898]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1507330 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1507330 = ⟨1254921187, 1082611351⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_753665]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1572866 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1572866 = ⟨1840729829, 2054753050⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_786433]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1572868 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1572868 = ⟨1331030264, 1995466708⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_786434]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1572872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1572872 = ⟨1852449998, 1719696311⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_786436]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1572880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1572880 = ⟨524724946, 1482509954⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_786440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1638402 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1638402 = ⟨1736038331, 937566682⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_819201]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1703938 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1703938 = ⟨511176002, 114411152⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_851969]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1703940 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1703940 = ⟨1218160061, 1612091480⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_851970]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1769474 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1769474 = ⟨1336607226, 1192095707⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_884737]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1835010 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1835010 = ⟨225601528, 141267527⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_917505]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1835012 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1835012 = ⟨559559014, 655192532⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_917506]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1835016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1835016 = ⟨728887635, 1230746836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_917508]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1900546 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1900546 = ⟨568417004, 2049797756⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_950273]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1966082 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1966082 = ⟨745663935, 594239492⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_983041]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1966084 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1966084 = ⟨1725298578, 1654060046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_983042]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2031618 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2031618 = ⟨2139664544, 1417621774⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1015809]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2097156 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2097156 = ⟨1668846927, 1207057547⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1048578]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2097160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2097160 = ⟨199050331, 405136431⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1048580]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2097168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2097168 = ⟨1349973308, 82240390⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1048584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2097184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2097184 = ⟨22895751, 1009463987⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1048592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2097216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2097216 = ⟨843834046, 974547238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1048608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2228228 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2228228 = ⟨1245604320, 1610324479⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1114114]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2359300 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2359300 = ⟨1089922728, 783093741⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1179650]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2359304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2359304 = ⟨685186593, 150853566⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1179652]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2490372 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2490372 = ⟨24351491, 2098890744⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1245186]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2621444 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2621444 = ⟨613085209, 2097604887⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1310722]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2621448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2621448 = ⟨717940527, 889911162⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1310724]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2621456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2621456 = ⟨1373040777, 738168110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1310728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2752516 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2752516 = ⟨605396552, 1833903068⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1376258]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2883588 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2883588 = ⟨1601299270, 350245313⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1441794]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2883592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2883592 = ⟨1490763399, 949035808⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1441796]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3014660 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3014660 = ⟨1574476414, 1971829352⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1507330]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3145732 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3145732 = ⟨126034806, 879928451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1572866]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3145736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3145736 = ⟨331180790, 204591913⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1572868]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3145744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3145744 = ⟨1312995862, 32859879⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1572872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3145760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3145760 = ⟨15723530, 2074097974⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1572880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3276804 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3276804 = ⟨1685085066, 1067971294⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1638402]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3407876 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3407876 = ⟨1560271150, 1257250472⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1703938]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3407880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3407880 = ⟨783682179, 787850191⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1703940]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3538948 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3538948 = ⟨1126942231, 1411202365⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1769474]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3670020 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3670020 = ⟨1762019134, 1596027536⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1835010]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3670024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3670024 = ⟨870443859, 162780334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1835012]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3670032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3670032 = ⟨1057270004, 1222812030⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1835016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3801092 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3801092 = ⟨674566758, 605587171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1900546]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3932164 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3932164 = ⟨1840241334, 1713474851⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1966082]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3932168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3932168 = ⟨637202177, 618108083⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1966084]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4063236 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4063236 = ⟨1172072684, 766602834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2031618]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4194312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4194312 = ⟨1893993951, 371027836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2097156]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4194320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4194320 = ⟨1425014060, 1405694276⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2097160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4194336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4194336 = ⟨1638010449, 1097522099⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2097168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4194368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4194368 = ⟨1393955190, 1062638423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2097184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4194432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4194432 = ⟨1607923274, 1825935004⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2097216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4456456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4456456 = ⟨1051957683, 1333604565⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2228228]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4718600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4718600 = ⟨2002133583, 111141995⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2359300]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4718608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4718608 = ⟨2013477176, 383977167⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2359304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4980744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4980744 = ⟨1581601118, 40654075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2490372]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5242888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5242888 = ⟨488849564, 1821635980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2621444]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5242896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5242896 = ⟨1115719669, 2091149163⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2621448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5242912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5242912 = ⟨1522611544, 493260231⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2621456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5505032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5505032 = ⟨1202864605, 746662970⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2752516]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5767176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5767176 = ⟨1366905769, 1160583961⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2883588]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5767184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5767184 = ⟨803025253, 1566565364⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2883592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6029320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6029320 = ⟨1163135514, 1236770571⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3014660]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6291464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6291464 = ⟨138195262, 1088781434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3145732]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6291472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6291472 = ⟨1173352677, 384608513⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3145736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6291488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6291488 = ⟨619372271, 1161198561⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3145744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6291520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6291520 = ⟨681600049, 1721989759⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3145760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6553608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6553608 = ⟨815181848, 1575081928⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3276804]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6815752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6815752 = ⟨1793693621, 1104712568⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3407876]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6815760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6815760 = ⟨796701433, 818672087⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3407880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7077896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7077896 = ⟨612561106, 817987856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3538948]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7340040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7340040 = ⟨969900137, 1016828605⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3670020]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7340048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7340048 = ⟨1316890203, 684517939⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3670024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7340064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7340064 = ⟨1548713494, 1001233851⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3670032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7602184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7602184 = ⟨408912969, 388934626⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3801092]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7864328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7864328 = ⟨861525751, 1324879591⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3932164]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7864336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7864336 = ⟨79149113, 315521296⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3932168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8126472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8126472 = ⟨1032023150, 1805037300⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4063236]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8388624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8388624 = ⟨1930571185, 1081942729⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4194312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8388640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8388640 = ⟨365525918, 78878415⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4194320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8388672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8388672 = ⟨395493632, 771634528⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4194336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8388736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8388736 = ⟨1993279917, 1922007123⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4194368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8388864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8388864 = ⟨1222219766, 827641544⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4194432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8912912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8912912 = ⟨1050728477, 288308279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4456456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9437200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9437200 = ⟨1709108292, 228171049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4718600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9437216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9437216 = ⟨692064060, 2096239⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4718608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9961488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9961488 = ⟨132982560, 2083846916⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4980744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10485776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10485776 = ⟨858833943, 1557142634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5242888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10485792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10485792 = ⟨1736620923, 272935180⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5242896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10485824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10485824 = ⟨877447629, 150263797⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5242912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11010064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11010064 = ⟨1289577522, 1308561988⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5505032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11534352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11534352 = ⟨770313446, 1557280514⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5767176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11534368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11534368 = ⟨1939833014, 1409968415⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5767184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12058640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12058640 = ⟨369473898, 1858858583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6029320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12582928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12582928 = ⟨1620900836, 1188247941⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6291464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12582944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12582944 = ⟨217398446, 1932743695⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6291472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12582976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12582976 = ⟨594173695, 567685145⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6291488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12583040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12583040 = ⟨45527540, 305103502⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6291520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13107216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13107216 = ⟨1332047726, 1219617528⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6553608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13631504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13631504 = ⟨2103125775, 1487347837⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6815752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13631520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13631520 = ⟨1005225526, 1736984945⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6815760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14155792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14155792 = ⟨611922777, 2139510620⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7077896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14680080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14680080 = ⟨212243360, 2025877123⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7340040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14680096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14680096 = ⟨1458224854, 661900689⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7340048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14680128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14680128 = ⟨1149255939, 1083761346⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7340064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15204368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15204368 = ⟨1314581349, 1416573066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7602184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15728656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15728656 = ⟨1437823319, 1100053461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7864328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15728672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15728672 = ⟨1551433675, 1144769845⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7864336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16252944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16252944 = ⟨1612813081, 1446823718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8126472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16777248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16777248 = ⟨1157415456, 427552688⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8388624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16777280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16777280 = ⟨319102580, 692112410⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8388640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16777344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16777344 = ⟨1940966201, 2129367498⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8388672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16777472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16777472 = ⟨550850371, 1272869949⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8388736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16777728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16777728 = ⟨91011709, 572815792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8388864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17825824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17825824 = ⟨178986373, 333539049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8912912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18874400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18874400 = ⟨841057873, 1981866202⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9437200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18874432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18874432 = ⟨1214676930, 338162627⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9437216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19922976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19922976 = ⟨1869666131, 1048839316⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9961488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20971552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20971552 = ⟨983060942, 115604005⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10485776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20971584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20971584 = ⟨2145104049, 1668396214⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10485792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20971648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20971648 = ⟨475283552, 470435543⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10485824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22020128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22020128 = ⟨124190551, 83687208⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11010064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23068704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23068704 = ⟨53294937, 86133140⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11534352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23068736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23068736 = ⟨511166171, 1849860057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11534368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24117280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24117280 = ⟨7385027, 1759584485⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12058640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25165856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25165856 = ⟨2102016731, 537645773⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12582928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25165888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25165888 = ⟨159100669, 221665758⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12582944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25165952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25165952 = ⟨611421363, 1903398164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12582976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25166080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25166080 = ⟨627316164, 935764080⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12583040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26214432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26214432 = ⟨1696084579, 1032906902⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13107216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27263008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27263008 = ⟨1455929384, 670995416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13631504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27263040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27263040 = ⟨1111550369, 333598410⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13631520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28311584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28311584 = ⟨1302751531, 1876719465⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14155792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29360160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29360160 = ⟨331509994, 557249567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14680080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29360192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29360192 = ⟨1627321260, 1231502258⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14680096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29360256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29360256 = ⟨542545724, 1038072030⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14680128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30408736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30408736 = ⟨786123425, 1665212150⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15204368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31457312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31457312 = ⟨1651667791, 1977566273⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15728656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31457344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31457344 = ⟨1902696988, 904789986⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15728672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32505888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32505888 = ⟨307510218, 2112418225⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16252944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33554496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33554496 = ⟨1321601726, 876281847⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16777248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33554560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33554560 = ⟨1576391580, 1943378136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16777280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33554688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33554688 = ⟨1552427031, 1967860929⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16777344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33554944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33554944 = ⟨216591688, 1453102685⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16777472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33555456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33555456 = ⟨119109612, 1742172267⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16777728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35651648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35651648 = ⟨804393196, 1813780376⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17825824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37748800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37748800 = ⟨1039810223, 686690941⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18874400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37748864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37748864 = ⟨781935012, 916072368⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18874432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39845952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39845952 = ⟨1904556974, 262586694⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19922976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41943104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41943104 = ⟨1663926865, 829488766⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20971552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41943168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41943168 = ⟨1292012576, 1707418088⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20971584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41943296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41943296 = ⟨720006972, 1017252335⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20971648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44040256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44040256 = ⟨1960840381, 2093309768⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22020128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46137408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46137408 = ⟨782964483, 599653607⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23068704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46137472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46137472 = ⟨715401544, 1635565228⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23068736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48234560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48234560 = ⟨110699386, 1527373022⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24117280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50331712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50331712 = ⟨1502493362, 2130694554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25165856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50331776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50331776 = ⟨1390249038, 2027984387⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25165888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50331904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50331904 = ⟨1265963536, 1982296770⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25165952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50332160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50332160 = ⟨1808519629, 1452153235⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25166080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52428864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52428864 = ⟨1420168384, 307130849⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26214432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54526016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54526016 = ⟨1526610602, 606050515⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27263008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54526080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54526080 = ⟨402854452, 396909113⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27263040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56623168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56623168 = ⟨942061619, 2078825111⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28311584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58720320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58720320 = ⟨654634383, 1900978770⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29360160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58720384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58720384 = ⟨1971374533, 42165738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29360192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58720512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58720512 = ⟨2074523778, 1096818517⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29360256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60817472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60817472 = ⟨1690115371, 660475456⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30408736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62914624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62914624 = ⟨1543991951, 441659571⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31457312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62914688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62914688 = ⟨438195227, 1863152581⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31457344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65011776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65011776 = ⟨1783449413, 926694571⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32505888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_67108992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67108992 = ⟨766241033, 1508951525⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33554496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_67109120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67109120 = ⟨687287640, 1841669638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33554560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_67109376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67109376 = ⟨1396111630, 2356285⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33554688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_67109888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67109888 = ⟨1601663285, 2022005567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33554944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71303296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71303296 = ⟨1921503113, 320604259⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35651648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_75497600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 75497600 = ⟨38752569, 473482900⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37748800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_75497728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 75497728 = ⟨1167865784, 1048155820⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37748864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_79691904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79691904 = ⟨583460003, 1581515145⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39845952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_83886208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83886208 = ⟨189900489, 1155724678⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41943104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_83886336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83886336 = ⟨1460676934, 544437191⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41943168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_83886592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83886592 = ⟨282147036, 774265443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41943296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88080512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88080512 = ⟨2083767704, 506984615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44040256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92274816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92274816 = ⟨1244581508, 1955563945⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46137408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92274944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92274944 = ⟨842621889, 1217545323⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46137472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_96469120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96469120 = ⟨1244352859, 1787427415⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48234560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_100663424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100663424 = ⟨1529550555, 1397177781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50331712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_100663552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100663552 = ⟨1097052486, 1295950705⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50331776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_100663808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100663808 = ⟨549698171, 1840512050⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50331904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_100664320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100664320 = ⟨1068288753, 675427495⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50332160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104857728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104857728 = ⟨54177866, 1079664148⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52428864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_109052032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109052032 = ⟨2129782951, 491159976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54526016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_109052160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109052160 = ⟨1711866603, 525004700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54526080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_113246336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 113246336 = ⟨949915159, 1113026051⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56623168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_117440640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117440640 = ⟨1302212008, 34197509⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58720320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_117440768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117440768 = ⟨1137297428, 115446572⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58720384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_117441024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117441024 = ⟨1645005707, 1630866518⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58720512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121634944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121634944 = ⟨2016588904, 1363841911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60817472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125829248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125829248 = ⟨41992699, 2012510771⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62914624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125829376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125829376 = ⟨647243878, 340642517⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62914688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_130023552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 130023552 = ⟨1598229142, 649856165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65011776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_134217984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 134217984 = ⟨1088836122, 1027974669⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67108992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_134218240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 134218240 = ⟨703123407, 2048375926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67109120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_134218752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 134218752 = ⟨479936188, 217587789⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67109376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_142606592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 142606592 = ⟨1785635372, 1882034175⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71303296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_150995200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 150995200 = ⟨1039897793, 1599002114⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75497600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_150995456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 150995456 = ⟨343375348, 723129461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75497728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_159383808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 159383808 = ⟨462634136, 612044910⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79691904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_167772416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 167772416 = ⟨2109148449, 1909078370⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83886208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_167772672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 167772672 = ⟨2101277330, 557724161⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83886336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_167773184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 167773184 = ⟨1276985988, 456990464⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83886592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_176161024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 176161024 = ⟨388979727, 475475962⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88080512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_184549632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 184549632 = ⟨839763948, 1768499389⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92274816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_184549888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 184549888 = ⟨353078869, 168772652⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92274944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_192938240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 192938240 = ⟨1791866405, 1865723249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96469120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_201326848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 201326848 = ⟨1159161011, 435031303⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100663424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_201327104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 201327104 = ⟨144365992, 1989514405⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100663552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_201327616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 201327616 = ⟨1329069890, 1640136239⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100663808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_209715456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 209715456 = ⟨772104479, 300491553⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104857728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_218104064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 218104064 = ⟨2139508819, 895426655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109052032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_218104320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 218104320 = ⟨331989508, 2049846847⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109052160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_226492672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 226492672 = ⟨949620120, 1076229102⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_113246336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_234881280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 234881280 = ⟨1160454477, 1789370499⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117440640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_234881536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 234881536 = ⟨1331395128, 865441511⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117440768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_234882048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 234882048 = ⟨1542630618, 1177056098⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117441024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_243269888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 243269888 = ⟨1363353906, 790586521⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121634944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_251658496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 251658496 = ⟨1947330394, 1566146139⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125829248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_251658752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 251658752 = ⟨534861883, 1273324256⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125829376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_260047104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 260047104 = ⟨1270050159, 850919294⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_130023552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_268435968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 268435968 = ⟨65615450, 772027800⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_134217984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_268436480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 268436480 = ⟨1462922215, 117240331⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_134218240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_285213184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 285213184 = ⟨437692305, 1603902647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_142606592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_301990400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 301990400 = ⟨1104339845, 1418381747⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_150995200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_301990912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 301990912 = ⟨1949036272, 2084561085⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_150995456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_318767616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 318767616 = ⟨1974518361, 602073794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_159383808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_335544832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 335544832 = ⟨1990579034, 2107059436⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_167772416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_335545344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 335545344 = ⟨1715132412, 1963268365⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_167772672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_352322048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 352322048 = ⟨1235205879, 281255253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_176161024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_369099264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 369099264 = ⟨1532431991, 551275760⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_184549632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_369099776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 369099776 = ⟨2144102382, 886761621⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_184549888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_385876480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 385876480 = ⟨1810973505, 543522600⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_192938240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_402653696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 402653696 = ⟨1176708096, 1985204270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_201326848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_402654208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 402654208 = ⟨797223315, 1892184156⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_201327104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_419430912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 419430912 = ⟨1228193681, 1262524066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_209715456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_436208128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 436208128 = ⟨306847357, 532095999⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_218104064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_436208640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 436208640 = ⟨818046810, 1849544479⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_218104320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_452985344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 452985344 = ⟨1765842714, 1525380355⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_226492672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_469762560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 469762560 = ⟨925302576, 1568599546⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_234881280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_469763072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 469763072 = ⟨1052324090, 1064735370⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_234881536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_486539776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 486539776 = ⟨2015497719, 907929188⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_243269888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_503316992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 503316992 = ⟨143655665, 240608314⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_251658496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_503317504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 503317504 = ⟨270443035, 1665395253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_251658752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_520094208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 520094208 = ⟨1569582022, 89304068⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_260047104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_536871936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 536871936 = ⟨788094511, 1125232586⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_268435968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_570426368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 570426368 = ⟨1742172267, 2028374035⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_285213184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_603980800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 603980800 = ⟨2022005567, 545820362⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_301990400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_637535232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 637535232 = ⟨675427495, 1079194894⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_318767616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_671089664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 671089664 = ⟨217587789, 1667547459⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_335544832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_704644096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 704644096 = ⟨456990464, 870497659⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_352322048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_738198528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 738198528 = ⟨1640136239, 818413757⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_369099264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_771752960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 771752960 = ⟨1177056098, 604853029⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_385876480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_805307392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 805307392 = ⟨117240331, 684561432⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_402653696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_838861824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 838861824 = ⟨2084561085, 198447375⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_419430912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_872416256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 872416256 = ⟨1963268365, 432351235⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_436208128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_905970688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 905970688 = ⟨886761621, 3381265⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_452985344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_939525120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 939525120 = ⟨1892184156, 1350260332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_469762560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_973079552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 973079552 = ⟨1849544479, 1329436837⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_486539776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1006633984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1006633984 = ⟨1064735370, 1095159557⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_503316992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1040188416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1040188416 = ⟨1665395253, 1877040612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_520094208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 0) = ⟨1022251061, 788094511⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 0 = 1024 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1024

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 1) = ⟨788094511, 1125232586⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 1 = 536871936 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_536871936

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 2) = ⟨1462922215, 117240331⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 2 = 268436480 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_268436480

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 3) = ⟨117240331, 684561432⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 3 = 805307392 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_805307392

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 4) = ⟨479936188, 217587789⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 4 = 134218752 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_134218752

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 5) = ⟨217587789, 1667547459⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 5 = 671089664 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_671089664

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 6) = ⟨797223315, 1892184156⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 6 = 402654208 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_402654208

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 7) = ⟨1892184156, 1350260332⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 7 = 939525120 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_939525120

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 8) = ⟨1601663285, 2022005567⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 8 = 67109888 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_67109888

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 9) = ⟨2022005567, 545820362⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 9 = 603980800 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_603980800

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 10) = ⟨1715132412, 1963268365⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 10 = 335545344 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_335545344

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 11) = ⟨1963268365, 432351235⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 11 = 872416256 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_872416256

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 12) = ⟨1329069890, 1640136239⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 12 = 201327616 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_201327616

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 13) = ⟨1640136239, 818413757⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 13 = 738198528 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_738198528

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 14) = ⟨1052324090, 1064735370⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 14 = 469763072 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_469763072

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 15) = ⟨1064735370, 1095159557⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 15 = 1006633984 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1006633984

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 16) = ⟨119109612, 1742172267⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 16 = 33555456 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_33555456

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 17) = ⟨1742172267, 2028374035⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 17 = 570426368 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_570426368

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 18) = ⟨1949036272, 2084561085⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 18 = 301990912 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_301990912

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 19) = ⟨2084561085, 198447375⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 19 = 838861824 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_838861824

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 20) = ⟨1276985988, 456990464⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 20 = 167773184 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_167773184

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 21) = ⟨456990464, 870497659⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 21 = 704644096 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_704644096

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 22) = ⟨818046810, 1849544479⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 22 = 436208640 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_436208640

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 23) = ⟨1849544479, 1329436837⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 23 = 973079552 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_973079552

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 24) = ⟨1068288753, 675427495⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 24 = 100664320 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_100664320

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 25) = ⟨675427495, 1079194894⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 25 = 637535232 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_637535232

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 26) = ⟨2144102382, 886761621⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 26 = 369099776 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_369099776

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 27) = ⟨886761621, 3381265⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 27 = 905970688 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_905970688

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 28) = ⟨1542630618, 1177056098⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 28 = 234882048 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_234882048

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 29) = ⟨1177056098, 604853029⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 29 = 771752960 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_771752960

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 30) = ⟨270443035, 1665395253⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 30 = 503317504 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_503317504

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 31) = ⟨1665395253, 1877040612⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 31 = 1040188416 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1040188416

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1022251061, 788094511⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 0) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

#print axioms entry_00
#print axioms entry_00_zPow

end R17TableAChunk00Certificate
