import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableBChunk08Certificate
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

theorem power_33 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33 = ⟨1913739346, 534400073⟩ := by
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

theorem power_49 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49 = ⟨173329971, 658630173⟩ := by
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

theorem power_65 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65 = ⟨1106294891, 184370010⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66 = ⟨235324384, 1522698391⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33]
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

theorem power_81 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81 = ⟨1283630603, 1419035398⟩ := by
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

theorem power_97 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 97 = ⟨1433319239, 2069664066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98 = ⟨1757883680, 2146872443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49]
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

theorem power_113 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 113 = ⟨1539908113, 1295392627⟩ := by
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

theorem power_129 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 129 = ⟨635733977, 1147342686⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_130 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 130 = ⟨182745460, 1218067210⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_132 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 132 = ⟨198245992, 796735524⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66]
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

theorem power_145 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 145 = ⟨1560614480, 360987849⟩ := by
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

theorem power_161 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 161 = ⟨1737405672, 316991337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_162 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 162 = ⟨154394112, 954850232⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81]
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

theorem power_177 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 177 = ⟨1360111873, 1045548151⟩ := by
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

theorem power_193 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 193 = ⟨631469289, 1565061397⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_194 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 194 = ⟨1182794174, 308889576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_97]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_196 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 196 = ⟨183649925, 520581699⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98]
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

theorem power_209 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 209 = ⟨1797275270, 153051719⟩ := by
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

theorem power_225 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 225 = ⟨601212348, 1809065373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_226 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 226 = ⟨907508540, 886854930⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_113]
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

theorem power_241 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 241 = ⟨1081438383, 1299194113⟩ := by
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

theorem power_257 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 257 = ⟨1781606919, 1263921092⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_258 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 258 = ⟨262969597, 504539214⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_129]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_260 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 260 = ⟨1113083573, 364920195⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_130]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 264 = ⟨768841324, 1818863266⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_132]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 272 = ⟨1106204247, 1950210306⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_273 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 273 = ⟨1331511067, 715482411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_289 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 289 = ⟨1407586475, 622260363⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_290 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 290 = ⟨156662592, 909666249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_145]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_305 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 305 = ⟨1882191182, 763421945⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_321 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 321 = ⟨853837217, 2147123310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_322 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 322 = ⟨1778301183, 2036177926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_161]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_324 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 324 = ⟨1784332407, 479339180⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_162]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_337 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 337 = ⟨488669925, 1257664401⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_353 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 353 = ⟨455425160, 639433327⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_354 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 354 = ⟨1847155883, 1096249344⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_177]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_369 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 369 = ⟨635537187, 1294233728⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_385 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 385 = ⟨895022962, 2113043113⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_386 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 386 = ⟨1985386694, 853298120⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_193]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_388 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 388 = ⟨430904798, 52332054⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_194]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 392 = ⟨396447072, 406060497⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_196]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_401 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 401 = ⟨639326768, 920544461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_417 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 417 = ⟨1087758747, 2140543891⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_418 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 418 = ⟨484064663, 997873469⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_209]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_433 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 433 = ⟨756425310, 1863576495⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_449 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 449 = ⟨2123406580, 2146492177⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_450 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 450 = ⟨724983407, 589107293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_225]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_452 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 452 = ⟨233641138, 250640687⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_226]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_465 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 465 = ⟨1008240277, 931344425⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_481 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 481 = ⟨226370743, 455167356⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_482 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 482 = ⟨604694560, 1964390835⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_241]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_497 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 497 = ⟨1059925606, 108581787⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 512 = ⟨6346213, 905523693⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_514 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 514 = ⟨56334686, 1422336979⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_257]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_516 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 516 = ⟨782339391, 1827324837⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_258]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 520 = ⟨1443640351, 1408176577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_260]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 528 = ⟨765837868, 957818106⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 544 = ⟨1192151435, 1028938634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_546 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 546 = ⟨147019096, 651086935⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_273]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_578 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 578 = ⟨447716021, 1998179775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_289]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_580 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 580 = ⟨369747845, 887373134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_290]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_610 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 610 = ⟨1074578953, 872532865⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_305]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_642 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 642 = ⟨160014150, 1681687122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_321]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_644 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 644 = ⟨1257431253, 699273795⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_322]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 648 = ⟨293244124, 1145620673⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_324]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_674 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 674 = ⟨1234979028, 1183882368⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_337]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_706 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 706 = ⟨113479996, 1919845475⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_353]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_708 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 708 = ⟨457829643, 1941425476⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_354]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_738 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 738 = ⟨2015607948, 1967565576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_369]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_770 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 770 = ⟨798110472, 1272135285⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_385]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_772 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 772 = ⟨1798781646, 1865266823⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_386]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 776 = ⟨286458136, 172269328⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_388]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 784 = ⟨1560235557, 1166001668⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_802 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 802 = ⟨1652299976, 841969630⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_401]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_834 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 834 = ⟨657339820, 1075594986⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_417]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_836 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 836 = ⟨83655737, 2124043286⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_418]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_866 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 866 = ⟨290282755, 865074362⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_433]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_898 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 898 = ⟨1069498853, 522796876⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_449]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_900 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 900 = ⟨612410710, 136959994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_450]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 904 = ⟨1367889452, 60689743⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_452]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_930 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 930 = ⟨1842260782, 1760640718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_465]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_962 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 962 = ⟨27798828, 187687974⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_481]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_964 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 964 = ⟨2118143742, 705646937⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_482]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_994 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 994 = ⟨1457960069, 1228264822⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_497]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1024 = ⟨1022251061, 788094511⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1028 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1028 = ⟨832050817, 965030129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_514]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1032 = ⟨1481817559, 1744156873⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_516]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1040 = ⟨1991902696, 973993416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1056 = ⟨1351366012, 1794883792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1088 = ⟨1453585800, 1686756607⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1092 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1092 = ⟨1111115265, 1136168241⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_546]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1156 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1156 = ⟨1426659191, 1053950497⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_578]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1160 = ⟨1896703716, 628956045⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_580]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1220 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1220 = ⟨338519872, 923797462⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_610]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1284 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1284 = ⟨292809474, 1236086310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_642]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1288 = ⟨1343759381, 1864045884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_644]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1296 = ⟨321437598, 88488468⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1348 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1348 = ⟨1390011110, 1152677708⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_674]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1412 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1412 = ⟨1213271284, 883965242⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_706]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1416 = ⟨1193898582, 1576714415⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_708]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1476 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1476 = ⟨332525602, 819252630⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_738]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1540 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1540 = ⟨32794988, 1407638922⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_770]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1544 = ⟨1068029906, 646532063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_772]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1552 = ⟨934314680, 892942796⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1568 = ⟨1111694799, 881760195⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1604 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1604 = ⟨1608070404, 1935826307⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_802]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1668 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1668 = ⟨303942118, 1253290941⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_834]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1672 = ⟨694287611, 660331636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_836]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1732 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1732 = ⟨2078266110, 483632041⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_866]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1796 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1796 = ⟨1960243961, 744591221⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_898]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1800 = ⟨1986113118, 992825915⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_900]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1808 = ⟨1868655533, 366044347⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1860 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1860 = ⟨1969457916, 875529778⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_930]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1924 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1924 = ⟨1400633973, 1825959484⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_962]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1928 = ⟨936181679, 1735398398⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_964]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1988 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1988 = ⟨1787682554, 26082154⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_994]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2048 = ⟨1633461177, 574296567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2056 = ⟨1623401953, 1768384744⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1028]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2064 = ⟨1860848169, 298938599⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2080 = ⟨1187370746, 926533015⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2112 = ⟨2063130879, 1272838818⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2176 = ⟨1655011431, 2085598907⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2184 = ⟨1673100658, 2028986703⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1092]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2312 = ⟨1308973632, 124370963⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1156]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2320 = ⟨280513604, 22556028⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2440 = ⟨1923457212, 820654477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1220]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2568 = ⟨64208596, 799665811⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1284]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2576 = ⟨910702273, 1588993839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2592 = ⟨1331074750, 1831714204⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2696 = ⟨21956735, 1588702434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1348]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2824 = ⟨936793321, 267330857⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1412]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2832 = ⟨1549367885, 715283423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2952 = ⟨262856771, 2081109767⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1476]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3080 = ⟨1923273678, 304490055⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1540]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3088 = ⟨1786181340, 1404427494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3104 = ⟨1341394939, 1875262719⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3136 = ⟨2017447582, 2138555804⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3208 = ⟨1460733615, 1152304641⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1604]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3336 = ⟨1875821749, 1293750591⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1668]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3344 = ⟨1194090073, 1501677440⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3464 = ⟨546752974, 716412508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1732]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3592 = ⟨1662873365, 2040801363⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1796]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3600 = ⟨1593351449, 859601116⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3616 = ⟨1520347037, 753194884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3720 = ⟨470408989, 1487021723⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1860]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3848 = ⟨1809052859, 880359647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1924]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3856 = ⟨288562008, 235863280⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3976 = ⟨77350242, 112557480⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1988]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4096 = ⟨595037635, 2111542451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4112 = ⟨118318128, 484833955⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4128 = ⟨152579518, 1401481845⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4160 = ⟨1624834588, 1587955294⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4224 = ⟨1810308513, 779811684⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4352 = ⟨718921583, 1008587178⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4368 = ⟨199033659, 1917543254⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4624 = ⟨733949038, 766830158⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4640 = ⟨1968119031, 1953739867⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4880 = ⟨1541852512, 1632290300⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5136 = ⟨799626643, 1791033603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5152 = ⟨915810530, 1384603928⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5184 = ⟨724607827, 1581281339⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5392 = ⟨2036021213, 142827219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5648 = ⟨270706650, 1042771289⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5664 = ⟨1026601736, 1271844727⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5904 = ⟨1924695146, 332717827⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6160 = ⟨1027613785, 1725744403⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6176 = ⟨315754747, 208044896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6208 = ⟨651225695, 496791815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6272 = ⟨1392302454, 203859073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6416 = ⟨558343669, 1875680288⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6672 = ⟨70723147, 2006869906⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6688 = ⟨769754617, 38321535⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6928 = ⟨1234333849, 78699212⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7184 = ⟨1265208484, 1628862338⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7200 = ⟨1184721950, 878005396⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7232 = ⟨1868836168, 945793409⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7440 = ⟨558085968, 1505322444⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7696 = ⟨102332793, 1065656622⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7712 = ⟨882289621, 2131737122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7952 = ⟨1691416901, 1575779874⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8224 = ⟨1760690870, 1674217597⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8256 = ⟨1893959686, 1568143280⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8320 = ⟨965135430, 672085251⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8448 = ⟨1508101166, 1752846715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8704 = ⟨252837685, 2006332926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8736 = ⟨1308873607, 1858041038⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9248 = ⟨765140296, 1916980574⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9280 = ⟨712478805, 1515677912⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9760 = ⟨1585274975, 766460784⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10272 = ⟨1222662793, 63527061⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10304 = ⟨1028494420, 870500944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10368 = ⟨801839679, 1416549508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10784 = ⟨1085986513, 364307406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11296 = ⟨201175544, 119528671⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11328 = ⟨451500757, 1042820697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11808 = ⟨1465803644, 1444946114⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12320 = ⟨1911608179, 383771197⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12352 = ⟨365044361, 1180771663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12416 = ⟨1634623176, 1242708781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12544 = ⟨1303271673, 1211882786⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12832 = ⟨1480961099, 1388756645⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13344 = ⟨607111232, 908919224⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13376 = ⟨1082234746, 1195886797⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13856 = ⟨413652689, 1223458076⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14368 = ⟨1618190802, 512344275⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14400 = ⟨852788928, 1407244314⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14464 = ⟨1919214175, 72145384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14880 = ⟨1066471087, 852741906⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15392 = ⟨1059063627, 348623094⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15424 = ⟨1562032226, 1259672017⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15904 = ⟨1954434689, 1242453461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16448 = ⟨743755452, 1309834646⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16512 = ⟨1291076935, 1070127583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16640 = ⟨71597582, 502509710⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16896 = ⟨1864067894, 380717230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17408 = ⟨913684129, 1336358039⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17472 = ⟨788330037, 877443746⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18496 = ⟨831676830, 1968879446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18560 = ⟨1694057790, 1757463169⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19520 = ⟨362546998, 964360007⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20544 = ⟨310712528, 2027511090⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20608 = ⟨1806350313, 1284788848⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20736 = ⟨753306136, 1377615667⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21568 = ⟨2036595798, 1456121490⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22592 = ⟨571532113, 423888331⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22656 = ⟨54122264, 999860590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23616 = ⟨1924624845, 679508361⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24640 = ⟨593985589, 1362046821⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24704 = ⟨872353324, 999049023⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24832 = ⟨1648510500, 90235145⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25088 = ⟨354002285, 308304222⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25664 = ⟨1116053913, 935251950⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26688 = ⟨1555956979, 1768038279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26752 = ⟨1177452963, 1170167703⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27712 = ⟨1533003397, 166659198⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28736 = ⟨591877865, 169971238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28800 = ⟨305787977, 153981243⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28928 = ⟨1228915707, 1186399647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29760 = ⟨1229853936, 1226491388⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30784 = ⟨942505556, 2094742780⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30848 = ⟨1625013772, 728500935⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31808 = ⟨1646825435, 1798860620⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32896 = ⟨56312003, 499779357⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33024 = ⟨1891007546, 749012277⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33280 = ⟨1263299221, 1709334650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33792 = ⟨2104985194, 631590980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34816 = ⟨1765678898, 2028236613⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34944 = ⟨79910836, 1808432265⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36992 = ⟨424128335, 2145867895⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37120 = ⟨167491913, 1919872944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39040 = ⟨1398005733, 290893644⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41088 = ⟨443237567, 597509638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41216 = ⟨1279689336, 292450238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41472 = ⟨2059141329, 885416319⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43136 = ⟨1153009698, 1168250033⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45184 = ⟨34829628, 1378122312⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45312 = ⟨452740335, 590580947⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47232 = ⟨1090047884, 1468303174⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49280 = ⟨1699475852, 991803471⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49408 = ⟨857744938, 166099594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49664 = ⟨845849999, 1932927210⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50176 = ⟨1062485927, 1068122241⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51328 = ⟨723275570, 584782387⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53376 = ⟨134053818, 241042193⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53504 = ⟨1164523761, 45068006⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55424 = ⟨2143612431, 83905258⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57472 = ⟨619779765, 1061154276⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57600 = ⟨1886078852, 330853404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57856 = ⟨922379982, 1084651240⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59520 = ⟨467878150, 1919832799⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61568 = ⟨17650825, 1578675031⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61696 = ⟨2110901694, 1683066232⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63616 = ⟨2031688949, 454537916⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65792 = ⟨1513437503, 595806186⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66048 = ⟨67188071, 768461072⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66560 = ⟨1581705852, 1303922066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_67584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67584 = ⟨2016807951, 234018695⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69632 = ⟨1964662320, 1382435771⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69888 = ⟨887254096, 1042278170⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73984 = ⟨1371178497, 1044573441⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_74240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 74240 = ⟨2081413072, 246071924⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_78080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 78080 = ⟨1293647959, 341256802⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_82176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 82176 = ⟨925362342, 26821273⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_82432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 82432 = ⟨321123339, 28578597⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_82944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 82944 = ⟨961560740, 1336435363⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_86272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86272 = ⟨2094834727, 1872863649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90368 = ⟨423692637, 574176990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90624 = ⟨898664610, 1196473364⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94464 = ⟨1358745474, 2083515698⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98560 = ⟨1748358559, 1331781942⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98816 = ⟨1094208192, 1382666258⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_99328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 99328 = ⟨1790091302, 24162003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_100352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100352 = ⟨1300335129, 1837567123⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102656 = ⟨199877240, 124858656⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106752 = ⟨1136363086, 655131482⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_107008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 107008 = ⟨603993480, 1658961978⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_110848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110848 = ⟨197376132, 228579220⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_114944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114944 = ⟨1793981867, 420728165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115200 = ⟨2115839553, 607309935⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115712 = ⟨1719401654, 122790862⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_119040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119040 = ⟨1450638869, 379059963⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123136 = ⟨128765964, 2100983575⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123392 = ⟨981855613, 2026394432⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_127232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 127232 = ⟨1868825675, 1584442183⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_131584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131584 = ⟨418125894, 1905639112⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_132096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 132096 = ⟨1545848211, 634791136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_133120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 133120 = ⟨1343125376, 1611076075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_135168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 135168 = ⟨798338207, 2110850421⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_139776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 139776 = ⟨31081231, 204215761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_147968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 147968 = ⟨730880720, 1670975189⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_148480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 148480 = ⟨1897626162, 1847676603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_156160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 156160 = ⟨776500164, 2060348201⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_164352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 164352 = ⟨1133201415, 1702257371⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_164864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 164864 = ⟨285695498, 613980118⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_165888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 165888 = ⟨821570021, 1145420705⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_172544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 172544 = ⟨472772772, 953649701⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_180736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 180736 = ⟨1629120760, 977300736⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_181248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 181248 = ⟨1395504571, 607335160⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_188928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 188928 = ⟨1187178865, 2044344996⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_197120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 197120 = ⟨1440683279, 1213702310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_197632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 197632 = ⟨1444784472, 1256093482⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_198656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 198656 = ⟨1408282706, 600722738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_200704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 200704 = ⟨1631496031, 481893475⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_205312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 205312 = ⟨801631504, 41759966⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_213504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 213504 = ⟨1753368112, 267503324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_214016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 214016 = ⟨715353272, 286494838⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_107008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_221696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 221696 = ⟨1851106838, 2025075705⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_229888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 229888 = ⟨1050324407, 1062605783⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_230400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 230400 = ⟨1365609705, 1009341282⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_231424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 231424 = ⟨1423034495, 1044300741⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_238080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 238080 = ⟨467927943, 617884096⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_246272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 246272 = ⟨1129488706, 384635748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_246784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 246784 = ⟨1038693574, 1287133297⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_254464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 254464 = ⟨187983652, 1630901003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_127232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_263168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 263168 = ⟨1349443438, 514129967⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_264192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 264192 = ⟨302125271, 1416107052⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_132096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_266240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 266240 = ⟨2008329732, 1737289791⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_279552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 279552 = ⟨1246195762, 1256466368⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_139776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_295936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 295936 = ⟨1913983391, 2022791627⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_147968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_296960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 296960 = ⟨295990997, 941692002⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_148480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_312320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 312320 = ⟨648795278, 1547325481⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_156160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_328704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 328704 = ⟨855944781, 184243911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_164352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_329728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 329728 = ⟨985045909, 786285443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_164864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_331776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 331776 = ⟨1250840269, 386418603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_165888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_345088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 345088 = ⟨1142957480, 959936799⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_172544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_361472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 361472 = ⟨1848179093, 834985707⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_180736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_362496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 362496 = ⟨966434100, 857433908⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_181248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_377856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 377856 = ⟨780302339, 1756370659⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_188928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_394240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 394240 = ⟨1123190600, 1491376626⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_197120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_395264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 395264 = ⟨1338663259, 1317602281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_197632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_397312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 397312 = ⟨1819903752, 1929668715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_198656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_410624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 410624 = ⟨947476152, 1518952731⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_205312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_427008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 427008 = ⟨1654980425, 82065982⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_213504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_428032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 428032 = ⟨492808319, 1202170691⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_214016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_443392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 443392 = ⟨2062545234, 1104223411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_221696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_459776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 459776 = ⟨1901516809, 612460964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_229888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_460800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 460800 = ⟨1180239345, 1380236185⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_230400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_462848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 462848 = ⟨422755315, 374503008⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_231424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_476160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 476160 = ⟨288387508, 1053507577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_238080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_492544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 492544 = ⟨1183422040, 1624215905⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_246272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_493568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 493568 = ⟨712896677, 412924820⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_246784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_508928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 508928 = ⟨1381116027, 853607054⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_254464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_526336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 526336 = ⟨1881642285, 2063950130⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_263168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_528384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 528384 = ⟨100684459, 1640456458⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_264192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_559104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 559104 = ⟨333497, 1196617052⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_279552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_591872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 591872 = ⟨1307842360, 1890785536⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_295936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_593920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 593920 = ⟨150937652, 383732090⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_296960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_624640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 624640 = ⟨868013894, 1609896752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_312320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_657408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 657408 = ⟨1456798835, 1310838394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_328704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_659456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 659456 = ⟨1789955189, 505997887⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_329728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_690176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 690176 = ⟨664296618, 511286472⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_345088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_722944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 722944 = ⟨962811294, 1542119379⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_361472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_724992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 724992 = ⟨168460970, 1615303811⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_362496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_755712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 755712 = ⟨6960782, 674583491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_377856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_788480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 788480 = ⟨490854036, 1299738414⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_394240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_790528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 790528 = ⟨1220431105, 100455014⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_395264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_821248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 821248 = ⟨1618314829, 1579390512⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_410624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_854016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 854016 = ⟨138411218, 355127523⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_427008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_856064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 856064 = ⟨332209582, 331411357⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_428032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_886784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 886784 = ⟨827672611, 312920181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_443392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_919552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 919552 = ⟨1701675353, 1983132973⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_459776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_921600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 921600 = ⟨683528853, 193776762⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_460800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_952320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 952320 = ⟨10399282, 1552502053⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_476160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_985088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 985088 = ⟨313826601, 1570162033⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_492544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_987136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 987136 = ⟨719706205, 1755223690⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_493568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1017856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1017856 = ⟨1816676196, 292450356⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_508928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1052672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1052672 = ⟨433157739, 937025459⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_526336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1118208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1118208 = ⟨1249682376, 474254021⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_559104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1183744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1183744 = ⟨1219048271, 773733831⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_591872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1249280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1249280 = ⟨964719250, 1012108343⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_624640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1314816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1314816 = ⟨748970643, 485565246⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_657408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1380352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1380352 = ⟨122969455, 311337502⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_690176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1445888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1445888 = ⟨354559414, 1412186133⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_722944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1511424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1511424 = ⟨1920015819, 2017323756⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_755712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1576960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1576960 = ⟨1936161103, 1911011743⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_788480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1642496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1642496 = ⟨588173577, 946133187⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_821248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1708032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1708032 = ⟨321157045, 133308492⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_854016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1773568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1773568 = ⟨1764389290, 1617898495⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_886784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1839104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1839104 = ⟨1661468032, 1401616134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_919552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1904640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1904640 = ⟨2021756148, 85056840⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_952320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1970176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1970176 = ⟨1371420477, 247094679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_985088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2035712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2035712 = ⟨1871020210, 2067959207⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1017856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 256) = ⟨595037635, 2111542451⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 256 = 4096 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_4096

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨595037635, 2111542451⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 256) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 257) = ⟨433157739, 937025459⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 257 = 1052672 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1052672

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨433157739, 937025459⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 257) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 258) = ⟨100684459, 1640456458⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 258 = 528384 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_528384

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨100684459, 1640456458⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 258) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 259) = ⟨1936161103, 1911011743⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 259 = 1576960 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1576960

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1936161103, 1911011743⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 259) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 260) = ⟨2008329732, 1737289791⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 260 = 266240 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_266240

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2008329732, 1737289791⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 260) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 261) = ⟨748970643, 485565246⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 261 = 1314816 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1314816

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨748970643, 485565246⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 261) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 262) = ⟨1220431105, 100455014⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 262 = 790528 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_790528

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1220431105, 100455014⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 262) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 263) = ⟨1661468032, 1401616134⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 263 = 1839104 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1839104

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1661468032, 1401616134⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 263) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 264) = ⟨798338207, 2110850421⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 264 = 135168 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_135168

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨798338207, 2110850421⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 264) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 265) = ⟨1219048271, 773733831⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 265 = 1183744 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1183744

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1219048271, 773733831⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 265) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 266) = ⟨1789955189, 505997887⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 266 = 659456 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_659456

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1789955189, 505997887⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 266) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 267) = ⟨321157045, 133308492⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 267 = 1708032 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1708032

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨321157045, 133308492⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 267) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 268) = ⟨1819903752, 1929668715⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 268 = 397312 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_397312

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1819903752, 1929668715⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 268) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 269) = ⟨354559414, 1412186133⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 269 = 1445888 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1445888

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨354559414, 1412186133⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 269) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 270) = ⟨683528853, 193776762⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 270 = 921600 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_921600

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨683528853, 193776762⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 270) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 271) = ⟨1371420477, 247094679⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 271 = 1970176 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1970176

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1371420477, 247094679⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 271) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 272) = ⟨1964662320, 1382435771⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 272 = 69632 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_69632

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1964662320, 1382435771⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 272) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 273) = ⟨1249682376, 474254021⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 273 = 1118208 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1118208

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1249682376, 474254021⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 273) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 274) = ⟨150937652, 383732090⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 274 = 593920 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_593920

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨150937652, 383732090⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 274) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 275) = ⟨588173577, 946133187⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 275 = 1642496 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1642496

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨588173577, 946133187⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 275) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 276) = ⟨1250840269, 386418603⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 276 = 331776 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_331776

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1250840269, 386418603⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 276) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 277) = ⟨122969455, 311337502⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 277 = 1380352 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1380352

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨122969455, 311337502⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 277) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 278) = ⟨332209582, 331411357⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 278 = 856064 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_856064

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨332209582, 331411357⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 278) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 279) = ⟨2021756148, 85056840⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 279 = 1904640 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1904640

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2021756148, 85056840⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 279) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 280) = ⟨1631496031, 481893475⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 280 = 200704 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_200704

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1631496031, 481893475⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 280) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 281) = ⟨964719250, 1012108343⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 281 = 1249280 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1249280

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨964719250, 1012108343⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 281) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 282) = ⟨168460970, 1615303811⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 282 = 724992 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_724992

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨168460970, 1615303811⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 282) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 283) = ⟨1764389290, 1617898495⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 283 = 1773568 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1773568

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1764389290, 1617898495⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 283) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 284) = ⟨422755315, 374503008⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 284 = 462848 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_462848

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨422755315, 374503008⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 284) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 285) = ⟨1920015819, 2017323756⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 285 = 1511424 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1511424

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1920015819, 2017323756⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 285) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 286) = ⟨719706205, 1755223690⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 286 = 987136 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_987136

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨719706205, 1755223690⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 286) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 287) = ⟨1871020210, 2067959207⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 287 = 2035712 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2035712

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1871020210, 2067959207⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 287) := by
  rw [← entry_31]
  exact fastPow_decode_zPow _

#print axioms entry_00
#print axioms entry_00_zPow
#print axioms entry_01
#print axioms entry_01_zPow
#print axioms entry_02
#print axioms entry_02_zPow
#print axioms entry_03
#print axioms entry_03_zPow
#print axioms entry_04
#print axioms entry_04_zPow
#print axioms entry_05
#print axioms entry_05_zPow
#print axioms entry_06
#print axioms entry_06_zPow
#print axioms entry_07
#print axioms entry_07_zPow
#print axioms entry_08
#print axioms entry_08_zPow
#print axioms entry_09
#print axioms entry_09_zPow
#print axioms entry_10
#print axioms entry_10_zPow
#print axioms entry_11
#print axioms entry_11_zPow
#print axioms entry_12
#print axioms entry_12_zPow
#print axioms entry_13
#print axioms entry_13_zPow
#print axioms entry_14
#print axioms entry_14_zPow
#print axioms entry_15
#print axioms entry_15_zPow
#print axioms entry_16
#print axioms entry_16_zPow
#print axioms entry_17
#print axioms entry_17_zPow
#print axioms entry_18
#print axioms entry_18_zPow
#print axioms entry_19
#print axioms entry_19_zPow
#print axioms entry_20
#print axioms entry_20_zPow
#print axioms entry_21
#print axioms entry_21_zPow
#print axioms entry_22
#print axioms entry_22_zPow
#print axioms entry_23
#print axioms entry_23_zPow
#print axioms entry_24
#print axioms entry_24_zPow
#print axioms entry_25
#print axioms entry_25_zPow
#print axioms entry_26
#print axioms entry_26_zPow
#print axioms entry_27
#print axioms entry_27_zPow
#print axioms entry_28
#print axioms entry_28_zPow
#print axioms entry_29
#print axioms entry_29_zPow
#print axioms entry_30
#print axioms entry_30_zPow
#print axioms entry_31
#print axioms entry_31_zPow

end R17TableBChunk08Certificate
