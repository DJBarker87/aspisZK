import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk08Certificate
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

theorem power_2049 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2049 = ⟨2131468039, 1090406455⟩ := by
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

theorem power_4098 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4098 = ⟨2063173026, 861579651⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2049]
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

theorem power_8196 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8196 = ⟨840339287, 845394660⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4098]
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

theorem power_16392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16392 = ⟨94365453, 406713819⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8196]
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

theorem power_32784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32784 = ⟨702249198, 1042782950⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16392]
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

theorem power_34817 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34817 = ⟨1043497430, 1431972154⟩ := by
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

theorem power_65568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65568 = ⟨1409818136, 218507227⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32784]
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

theorem power_67585 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67585 = ⟨1974291763, 1482799741⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69634 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69634 = ⟨2136260913, 367268992⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34817]
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

theorem power_100353 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100353 = ⟨528224131, 1825850831⟩ := by
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

theorem power_131136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131136 = ⟨946377862, 692619332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65568]
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

theorem power_133121 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 133121 = ⟨1181878471, 1757008669⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_135170 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 135170 = ⟨1892345818, 1922268035⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67585]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_139268 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 139268 = ⟨1832560058, 1741057821⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69634]
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

theorem power_165889 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 165889 = ⟨1894364491, 1744735901⟩ := by
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

theorem power_198657 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 198657 = ⟨1441636205, 1626332059⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_200706 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 200706 = ⟨321804692, 964655954⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100353]
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

theorem power_231425 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 231425 = ⟨1493162264, 1669576965⟩ := by
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

theorem power_262272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 262272 = ⟨2009996053, 824194071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_263168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 263168 = ⟨1349443438, 514129967⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_264193 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 264193 = ⟨655842966, 1721043143⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_132096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_266242 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 266242 = ⟨412898244, 1127341915⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133121]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_270340 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 270340 = ⟨852425230, 549330387⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_135170]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_278536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 278536 = ⟨160338056, 1406526960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_139268]
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

theorem power_296961 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 296961 = ⟨2077097216, 613013537⟩ := by
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

theorem power_329729 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 329729 = ⟨1877645743, 360869591⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_164864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_331778 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 331778 = ⟨218601447, 370461927⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_165889]
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

theorem power_362497 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 362497 = ⟨712647806, 1520754502⟩ := by
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

theorem power_395265 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 395265 = ⟨336934447, 25391983⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_197632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_397314 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 397314 = ⟨1569966733, 204473691⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_198657]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_401412 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 401412 = ⟨382738912, 769202055⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_200706]
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

theorem power_428033 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 428033 = ⟨1751441384, 658803012⟩ := by
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

theorem power_460801 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 460801 = ⟨825844976, 531390356⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_230400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_462850 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 462850 = ⟨1737947210, 179706813⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_231425]
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

theorem power_493569 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 493569 = ⟨592189950, 1658399919⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_246784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_508928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 508928 = ⟨1381116027, 853607054⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_254464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_524544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 524544 = ⟨496495591, 1832876818⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_262272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_526337 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 526337 = ⟨1816356622, 300541113⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_263168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_528386 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 528386 = ⟨1135444886, 495104952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_264193]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_532484 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 532484 = ⟨1846024394, 468834973⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_266242]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_540680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 540680 = ⟨1575269786, 1822280254⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_270340]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_557072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 557072 = ⟨1918887607, 951526207⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_278536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_559105 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 559105 = ⟨764315709, 199885542⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_279552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_591873 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 591873 = ⟨593497720, 1462040520⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_295936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_593922 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 593922 = ⟨1200642933, 381271897⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_296961]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_624641 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 624641 = ⟨1943653827, 241563735⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_312320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_657409 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 657409 = ⟨349776296, 1912121775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_328704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_659458 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 659458 = ⟨1746037838, 158963899⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_329729]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_663556 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 663556 = ⟨1076870013, 308486960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_331778]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_690177 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 690177 = ⟨2070513235, 1604354808⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_345088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_722945 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 722945 = ⟨2127824906, 1628399098⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_361472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_724994 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 724994 = ⟨1724421383, 469281127⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_362497]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_755713 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 755713 = ⟨795343984, 2012310691⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_377856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_788481 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 788481 = ⟨117768952, 1299167847⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_394240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_790530 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 790530 = ⟨346620454, 1269222206⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_395265]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_794628 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 794628 = ⟨1765047620, 195915493⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_397314]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_802824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 802824 = ⟨689488933, 867284007⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_401412]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_821249 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 821249 = ⟨1398471031, 2027843272⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_410624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_854017 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 854017 = ⟨2066639182, 559165392⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_427008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_856066 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 856066 = ⟨208960305, 1351255750⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_428033]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_886785 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 886785 = ⟨761691488, 1823886150⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_443392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_919553 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 919553 = ⟨2000164888, 583710469⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_459776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_921602 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 921602 = ⟨456448007, 1579365926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_460801]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_925700 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 925700 = ⟨247086614, 802722375⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_462850]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_952321 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 952321 = ⟨1493009792, 603225451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_476160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_985089 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 985089 = ⟨488672444, 587870590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_492544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_987138 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 987138 = ⟨1583269618, 706422718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_493569]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1017857 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1017857 = ⟨848179321, 1158101898⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_508928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1049088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1049088 = ⟨24570699, 709050038⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_524544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1052674 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1052674 = ⟨214191188, 449147368⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_526337]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1056772 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1056772 = ⟨139385270, 788382143⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_528386]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1064968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1064968 = ⟨188273925, 948283536⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_532484]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1081360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1081360 = ⟨1208361567, 932998863⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_540680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1114144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1114144 = ⟨1541727042, 1397148455⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_557072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1118210 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1118210 = ⟨1556572692, 1815925816⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_559105]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1183746 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1183746 = ⟨1764774013, 1944923688⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_591873]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1187844 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1187844 = ⟨614356857, 257654793⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_593922]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1249282 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1249282 = ⟨698705345, 111273167⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_624641]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1314818 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1314818 = ⟨1375278950, 1686581764⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_657409]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1318916 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1318916 = ⟨986690771, 1487613023⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_659458]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1327112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1327112 = ⟨46878885, 1212765883⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_663556]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1380354 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1380354 = ⟨1595688991, 50771089⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_690177]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1445890 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1445890 = ⟨1291247333, 1241216896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_722945]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1449988 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1449988 = ⟨812915725, 1856446929⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_724994]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1511426 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1511426 = ⟨423019960, 1596072971⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_755713]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1576962 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1576962 = ⟨1547090313, 971443269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_788481]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1581060 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1581060 = ⟨319593198, 821638374⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_790530]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1589256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1589256 = ⟨2126993971, 212379997⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_794628]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1605648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1605648 = ⟨148184982, 1941676992⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_802824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1642498 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1642498 = ⟨1981407999, 1146639754⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_821249]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1708034 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1708034 = ⟨1539878388, 762034685⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_854017]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1712132 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1712132 = ⟨1909244146, 900098861⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_856066]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1773570 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1773570 = ⟨1812106350, 1931547884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_886785]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1839106 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1839106 = ⟨396218180, 22195127⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_919553]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1843204 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1843204 = ⟨1910006344, 1019325257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_921602]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1851400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1851400 = ⟨1634790633, 2118263814⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_925700]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1904642 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1904642 = ⟨1157208932, 642462451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_952321]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1970178 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1970178 = ⟨905831479, 411890083⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_985089]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1974276 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1974276 = ⟨1674407497, 309282909⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_987138]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2035714 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2035714 = ⟨1321376261, 583600972⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1017857]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2098176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2098176 = ⟨785785922, 1967683322⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1049088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2105348 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2105348 = ⟨827321810, 2110497333⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1052674]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2113544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2113544 = ⟨154153562, 163768042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1056772]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2129936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2129936 = ⟨618291170, 1218535341⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1064968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2162720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2162720 = ⟨1932561517, 869436115⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1081360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2228288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2228288 = ⟨177099490, 198338273⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1114144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2236420 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2236420 = ⟨1956176241, 356006492⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1118210]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2367492 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2367492 = ⟨1363109541, 1342223992⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1183746]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2375688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2375688 = ⟨1400019081, 1365941608⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1187844]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2498564 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2498564 = ⟨1704021201, 63778976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1249282]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2629636 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2629636 = ⟨236799484, 994242877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1314818]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2637832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2637832 = ⟨1207035303, 2142085369⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1318916]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2654224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2654224 = ⟨642404255, 7904121⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1327112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2760708 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2760708 = ⟨1200286237, 594056573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1380354]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2891780 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2891780 = ⟨283769686, 35506469⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1445890]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2899976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2899976 = ⟨1113894410, 630013956⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1449988]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3022852 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3022852 = ⟨1855480278, 1286307481⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1511426]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3153924 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3153924 = ⟨224664279, 26247244⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1576962]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3162120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3162120 = ⟨1976690943, 187085988⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1581060]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3178512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3178512 = ⟨424094833, 368204483⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1589256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3211296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3211296 = ⟨1748723042, 520437523⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1605648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3284996 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3284996 = ⟨1075442567, 169120653⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1642498]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3416068 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3416068 = ⟨2055767310, 1764627669⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1708034]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3424264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3424264 = ⟨949051887, 2021890691⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1712132]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3547140 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3547140 = ⟨1405720725, 1431077830⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1773570]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3678212 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3678212 = ⟨992282167, 1720722435⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1839106]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3686408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3686408 = ⟨1761173286, 1566022252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1843204]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3702800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3702800 = ⟨110620037, 407611557⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1851400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3809284 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3809284 = ⟨1477096914, 1483558790⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1904642]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3940356 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3940356 = ⟨2044491983, 1239304411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1970178]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3948552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3948552 = ⟨679199291, 358121778⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1974276]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4071428 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4071428 = ⟨292073301, 1467001821⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2035714]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4210696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4210696 = ⟨924043395, 873415668⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2105348]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4227088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4227088 = ⟨10502588, 207914716⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2113544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4259872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4259872 = ⟨383491075, 1181084611⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2129936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4325440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4325440 = ⟨388065870, 1736876222⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2162720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4456576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4456576 = ⟨1826149741, 1626665850⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2228288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4472840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4472840 = ⟨500909614, 1713493832⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2236420]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4734984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4734984 = ⟨400590674, 1458765475⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2367492]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4751376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4751376 = ⟨43776886, 1238369639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2375688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4997128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4997128 = ⟨751659414, 1697699694⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2498564]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5259272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5259272 = ⟨2140175392, 582586880⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2629636]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5275664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5275664 = ⟨2042932660, 2027860331⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2637832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5308448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5308448 = ⟨1078435414, 1409414823⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2654224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5521416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5521416 = ⟨1991472006, 1599292209⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2760708]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5783560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5783560 = ⟨1997788895, 442163685⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2891780]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5799952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5799952 = ⟨1898149405, 740502822⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2899976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6045704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6045704 = ⟨908392681, 2060773348⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3022852]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6307848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6307848 = ⟨610142364, 1853537319⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3153924]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6324240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6324240 = ⟨230721632, 1322546162⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3162120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6357024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6357024 = ⟨180747680, 637287348⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3178512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6422592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6422592 = ⟨812004262, 420518149⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3211296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6569992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6569992 = ⟨809702389, 225703592⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3284996]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6832136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6832136 = ⟨1655224324, 1382010266⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3416068]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6848528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6848528 = ⟨2120855523, 62697569⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3424264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7094280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7094280 = ⟨327674936, 1747218187⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3547140]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7356424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7356424 = ⟨46241922, 2101728199⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3678212]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7372816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7372816 = ⟨1656796204, 2043678362⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3686408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7405600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7405600 = ⟨389608290, 101024238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3702800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7618568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7618568 = ⟨607303252, 1978076540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3809284]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7880712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7880712 = ⟨2107510544, 617995123⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3940356]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7897104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7897104 = ⟨1773835595, 1311239339⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3948552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8142856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8142856 = ⟨1929833681, 824392460⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4071428]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8421392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8421392 = ⟨73657552, 1020395968⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4210696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8454176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8454176 = ⟨2009306471, 1396757291⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4227088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8519744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8519744 = ⟨680869092, 1518323707⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4259872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8650880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8650880 = ⟨954037601, 1301134060⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4325440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8913152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8913152 = ⟨1557909445, 545665741⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4456576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8945680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8945680 = ⟨835716965, 179961656⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4472840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9469968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9469968 = ⟨787980670, 65759298⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4734984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9502752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9502752 = ⟨535064744, 538532592⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4751376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9994256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9994256 = ⟨1257098302, 1123486823⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4997128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10518544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10518544 = ⟨1050720975, 2030772889⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5259272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10551328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10551328 = ⟨447191643, 751080949⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5275664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10616896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10616896 = ⟨735319704, 46781663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5308448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11042832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11042832 = ⟨1865614705, 1826302496⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5521416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11567120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11567120 = ⟨880081334, 2064093298⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5783560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11599904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11599904 = ⟨14338895, 536990469⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5799952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12091408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12091408 = ⟨753336710, 1759671851⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6045704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12615696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12615696 = ⟨2053018103, 885202047⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6307848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12648480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12648480 = ⟨876659353, 1786274402⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6324240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12714048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12714048 = ⟨685476802, 45700420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6357024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12845184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12845184 = ⟨167841781, 24046062⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6422592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13139984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13139984 = ⟨1274901806, 480780326⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6569992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13664272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13664272 = ⟨1260515444, 195536889⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6832136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13697056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13697056 = ⟨1674385831, 1287196955⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6848528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14188560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14188560 = ⟨537161068, 470735619⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7094280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14712848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14712848 = ⟨769369900, 433751505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7356424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14745632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14745632 = ⟨2046573345, 2130899557⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7372816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14811200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14811200 = ⟨83068067, 791717025⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7405600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15237136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15237136 = ⟨1238387820, 1307348316⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7618568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15761424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15761424 = ⟨1741992753, 582193566⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7880712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15794208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15794208 = ⟨1254302149, 1954354387⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7897104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16285712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16285712 = ⟨1148774673, 356853970⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8142856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16842784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16842784 = ⟨137194397, 1730735618⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8421392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16908352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16908352 = ⟨1213450285, 1028058907⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8454176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17039488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17039488 = ⟨2038644283, 216712109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8519744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17301760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17301760 = ⟨1360931130, 312720909⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8650880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17826304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17826304 = ⟨2115453820, 111170389⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8913152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17891360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17891360 = ⟨57838388, 1444001617⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8945680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18939936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18939936 = ⟨1082075728, 1595540049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9469968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19005504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19005504 = ⟨696998149, 2086155744⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9502752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19988512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19988512 = ⟨590813670, 2089459913⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9994256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21037088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21037088 = ⟨1533797466, 1073417753⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10518544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21102656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21102656 = ⟨45161734, 1417181705⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10551328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21233792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21233792 = ⟨427864497, 2105800034⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10616896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22085664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22085664 = ⟨326916943, 1862489399⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11042832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23134240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23134240 = ⟨201721436, 1105602866⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11567120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23199808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23199808 = ⟨1208463548, 180066042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11599904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24182816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24182816 = ⟨1059948590, 1697665059⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12091408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25231392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25231392 = ⟨1261736158, 888062028⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12615696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25296960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25296960 = ⟨998374561, 284142898⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12648480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25428096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25428096 = ⟨780525019, 127025277⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12714048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25690368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25690368 = ⟨190944754, 701169712⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12845184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26279968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26279968 = ⟨1733828334, 1794165867⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13139984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27328544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27328544 = ⟨129435311, 751026364⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13664272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27394112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27394112 = ⟨531705479, 2108538171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13697056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28377120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28377120 = ⟨1146009817, 2032842479⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14188560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29425696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29425696 = ⟨1975563282, 2110852920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14712848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29491264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29491264 = ⟨969020969, 1030434629⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14745632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29622400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29622400 = ⟨1421283001, 1459897805⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14811200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30474272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30474272 = ⟨297955175, 988107957⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15237136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31522848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31522848 = ⟨295600749, 1885144273⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15761424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31588416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31588416 = ⟨209343547, 1164328293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15794208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32571424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32571424 = ⟨25278963, 589257317⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16285712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33685568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33685568 = ⟨636008372, 420212337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16842784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33816704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33816704 = ⟨1160093668, 1632388131⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16908352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34078976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34078976 = ⟨1908052900, 278025417⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17039488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34603520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34603520 = ⟨793225433, 1102990639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17301760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35652608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35652608 = ⟨2089806413, 155403522⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17826304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35782720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35782720 = ⟨2083688236, 1661685314⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17891360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37879872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37879872 = ⟨1169949515, 624492398⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18939936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38011008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38011008 = ⟨1673309606, 1121917389⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19005504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39977024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39977024 = ⟨575006987, 761607330⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19988512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42074176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42074176 = ⟨1483761290, 401425828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21037088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42205312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42205312 = ⟨2068427835, 692799932⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21102656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42467584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42467584 = ⟨114689628, 1104070085⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21233792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44171328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44171328 = ⟨606162074, 1001939989⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22085664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46268480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46268480 = ⟨1530078482, 1377128393⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23134240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46399616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46399616 = ⟨430400179, 551408433⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23199808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48365632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48365632 = ⟨1469551878, 2092140734⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24182816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50462784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50462784 = ⟨1488215996, 1266566902⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25231392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50593920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50593920 = ⟨1249078348, 1385538177⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25296960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50856192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50856192 = ⟨360003997, 1794448484⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25428096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51380736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51380736 = ⟨209015262, 500357215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25690368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52559936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52559936 = ⟨1033463659, 400814777⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26279968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54657088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54657088 = ⟨1101753377, 987217540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27328544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54788224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54788224 = ⟨838280697, 823189440⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27394112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56754240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56754240 = ⟨743504259, 1146625425⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28377120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58851392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58851392 = ⟨1945729316, 441051361⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29425696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58982528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58982528 = ⟨1748904240, 779532383⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29491264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59244800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59244800 = ⟨1523586463, 34852388⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29622400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60948544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60948544 = ⟨1914343619, 1084946387⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30474272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63045696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63045696 = ⟨2060944047, 2063949281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31522848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63176832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63176832 = ⟨1515476120, 523658828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31588416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65142848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65142848 = ⟨670518804, 1657357413⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32571424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_67371136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67371136 = ⟨446304189, 760403430⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33685568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_67633408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67633408 = ⟨1379876097, 96093434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33816704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_68157952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 68157952 = ⟨419724135, 207758524⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34078976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69207040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69207040 = ⟨778346524, 2089805548⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34603520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71565440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71565440 = ⟨730362332, 1867303095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35782720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_75759744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 75759744 = ⟨1415659358, 1132530479⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37879872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76022016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76022016 = ⟨1721857215, 495110290⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38011008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_79954048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79954048 = ⟨1384161514, 539280459⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39977024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_84148352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84148352 = ⟨2111464490, 803080737⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42074176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_84410624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84410624 = ⟨1653714134, 1831378055⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42205312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_84935168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84935168 = ⟨1688981258, 1715918353⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42467584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88342656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88342656 = ⟨1638211783, 744860702⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44171328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92536960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92536960 = ⟨789185746, 1495087165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46268480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92799232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92799232 = ⟨1299680564, 1963030151⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46399616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_96731264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96731264 = ⟨1737063540, 1952906431⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48365632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_100925568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100925568 = ⟨55322560, 1823814391⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50462784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_101187840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101187840 = ⟨718022585, 1038960924⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50593920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_101712384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101712384 = ⟨2015648022, 1452126297⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50856192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102761472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102761472 = ⟨10571466, 1530894063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51380736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105119872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105119872 = ⟨1185180232, 1207847817⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52559936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_109314176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109314176 = ⟨182826827, 2098673505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54657088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_109576448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109576448 = ⟨1665271023, 1045375243⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54788224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_113508480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 113508480 = ⟨2026893208, 1571119441⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56754240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_117702784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117702784 = ⟨1155428845, 507738381⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58851392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_117965056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117965056 = ⟨495653948, 1027972644⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58982528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_118489600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118489600 = ⟨1631769309, 568234924⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59244800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121897088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121897088 = ⟨375298000, 292179101⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60948544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126091392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126091392 = ⟨219733809, 884824527⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63045696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126353664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126353664 = ⟨2128990601, 27851459⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63176832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_130285696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 130285696 = ⟨1304790502, 330734270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65142848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_134742272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 134742272 = ⟨868614838, 1156549369⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67371136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_135266816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 135266816 = ⟨1539391184, 1924923173⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67633408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_136315904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 136315904 = ⟨1932511129, 687696804⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68157952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_143130880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 143130880 = ⟨1180984835, 491743376⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71565440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_151519488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 151519488 = ⟨2031527714, 1088637341⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75759744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_152044032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 152044032 = ⟨663455859, 1575124058⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76022016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_159908096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 159908096 = ⟨1487227556, 956583670⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79954048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_168296704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 168296704 = ⟨2095951431, 85597658⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84148352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_168821248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 168821248 = ⟨1174925996, 1732755504⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84410624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_169870336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 169870336 = ⟨1005915392, 1867478512⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84935168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_176685312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 176685312 = ⟨980085450, 1333902430⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88342656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_185073920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 185073920 = ⟨462500141, 703960232⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92536960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_185598464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 185598464 = ⟨372846647, 441135186⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92799232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_193462528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 193462528 = ⟨953211151, 887874220⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96731264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_201851136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 201851136 = ⟨1082367575, 1469418900⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100925568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_202375680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 202375680 = ⟨782386881, 725841211⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101187840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_203424768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 203424768 = ⟨2078867071, 276497442⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101712384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_210239744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 210239744 = ⟨1052292958, 412550878⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105119872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_218628352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 218628352 = ⟨414163390, 966639312⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109314176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_219152896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 219152896 = ⟨1687761311, 1566946423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109576448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_227016960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 227016960 = ⟨338213520, 31270436⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_113508480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_235405568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 235405568 = ⟨765059600, 350780571⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117702784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_235930112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 235930112 = ⟨858133681, 414741275⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117965056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_236979200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 236979200 = ⟨1461025413, 1421466600⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118489600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_243794176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 243794176 = ⟨895460909, 2021653733⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121897088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_252182784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 252182784 = ⟨775615255, 2056124521⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126091392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_252707328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 252707328 = ⟨1221728496, 1215786614⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126353664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_260571392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 260571392 = ⟨1250640150, 893911783⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_130285696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_269484544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 269484544 = ⟨352365498, 699771084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_134742272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_270533632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 270533632 = ⟨1302242334, 693913202⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_135266816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_286261760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 286261760 = ⟨1265173687, 132909193⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_143130880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_303038976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 303038976 = ⟨2063888645, 1378554486⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_151519488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_304088064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 304088064 = ⟨396887507, 760876211⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_152044032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_319816192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 319816192 = ⟨354331208, 1128304989⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_159908096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_336593408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 336593408 = ⟨1343333734, 1420456797⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_168296704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_337642496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 337642496 = ⟨1132767988, 594038315⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_168821248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_353370624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 353370624 = ⟨1385057010, 58950043⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_176685312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_370147840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 370147840 = ⟨79187634, 731995753⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_185073920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_371196928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 371196928 = ⟨1927076832, 605215390⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_185598464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_386925056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 386925056 = ⟨860160801, 1617379483⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_193462528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_403702272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 403702272 = ⟨519786109, 1613403898⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_201851136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_404751360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 404751360 = ⟨429857837, 1376073165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_202375680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_420479488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 420479488 = ⟨40306030, 2046015062⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_210239744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_437256704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 437256704 = ⟨1500425551, 1723998527⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_218628352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_438305792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 438305792 = ⟨1098427204, 880292698⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_219152896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_454033920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 454033920 = ⟨809808004, 885778⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_227016960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_470811136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 470811136 = ⟨1576950245, 389872801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_235405568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_471860224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 471860224 = ⟨22088804, 47256722⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_235930112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_487588352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 487588352 = ⟨1930150398, 1097595084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_243794176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_504365568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 504365568 = ⟨1139166174, 791995794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_252182784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_505414656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 505414656 = ⟨725035983, 816938404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_252707328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_521142784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 521142784 = ⟨1135841609, 717422501⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_260571392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_538969088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 538969088 = ⟨1967683322, 1361697725⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_269484544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_572523520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 572523520 = ⟨155403522, 57677234⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_286261760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_606077952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 606077952 = ⟨2089805548, 1369137123⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_303038976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_639632384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 639632384 = ⟨1530894063, 2136912181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_319816192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_673186816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 673186816 = ⟨687696804, 214972518⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_336593408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_706741248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 706741248 = ⟨1867478512, 1141568255⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_353370624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_740295680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 740295680 = ⟨276497442, 68616576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_370147840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_773850112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 773850112 = ⟨1421466600, 686458234⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_386925056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_807404544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 807404544 = ⟨693913202, 845241313⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_403702272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_840958976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 840958976 = ⟨760876211, 1750596140⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_420479488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_874513408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 874513408 = ⟨594038315, 1014715659⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_437256704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_908067840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 908067840 = ⟨605215390, 220406815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_454033920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_941622272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 941622272 = ⟨1376073165, 1717625810⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_470811136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_975176704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 975176704 = ⟨880292698, 1049056443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_487588352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1008731136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1008731136 = ⟨47256722, 2125394843⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_504365568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1042285568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1042285568 = ⟨816938404, 1422447664⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_521142784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 256) = ⟨785785922, 1967683322⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 256 = 2098176 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2098176

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨785785922, 1967683322⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 256) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 257) = ⟨1967683322, 1361697725⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 257 = 538969088 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_538969088

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1967683322, 1361697725⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 257) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 258) = ⟨1302242334, 693913202⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 258 = 270533632 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_270533632

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1302242334, 693913202⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 258) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 259) = ⟨693913202, 845241313⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 259 = 807404544 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_807404544

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨693913202, 845241313⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 259) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 260) = ⟨1932511129, 687696804⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 260 = 136315904 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_136315904

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1932511129, 687696804⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 260) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 261) = ⟨687696804, 214972518⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 261 = 673186816 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_673186816

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨687696804, 214972518⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 261) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 262) = ⟨429857837, 1376073165⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 262 = 404751360 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_404751360

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨429857837, 1376073165⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 262) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 263) = ⟨1376073165, 1717625810⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 263 = 941622272 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_941622272

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1376073165, 1717625810⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 263) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 264) = ⟨778346524, 2089805548⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 264 = 69207040 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_69207040

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨778346524, 2089805548⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 264) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 265) = ⟨2089805548, 1369137123⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 265 = 606077952 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_606077952

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2089805548, 1369137123⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 265) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 266) = ⟨1132767988, 594038315⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 266 = 337642496 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_337642496

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1132767988, 594038315⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 266) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 267) = ⟨594038315, 1014715659⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 267 = 874513408 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_874513408

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨594038315, 1014715659⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 267) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 268) = ⟨2078867071, 276497442⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 268 = 203424768 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_203424768

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2078867071, 276497442⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 268) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 269) = ⟨276497442, 68616576⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 269 = 740295680 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_740295680

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨276497442, 68616576⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 269) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 270) = ⟨22088804, 47256722⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 270 = 471860224 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_471860224

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨22088804, 47256722⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 270) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 271) = ⟨47256722, 2125394843⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 271 = 1008731136 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1008731136

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨47256722, 2125394843⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 271) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 272) = ⟨2089806413, 155403522⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 272 = 35652608 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_35652608

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2089806413, 155403522⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 272) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 273) = ⟨155403522, 57677234⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 273 = 572523520 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_572523520

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨155403522, 57677234⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 273) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 274) = ⟨396887507, 760876211⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 274 = 304088064 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_304088064

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨396887507, 760876211⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 274) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 275) = ⟨760876211, 1750596140⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 275 = 840958976 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_840958976

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨760876211, 1750596140⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 275) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 276) = ⟨1005915392, 1867478512⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 276 = 169870336 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_169870336

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1005915392, 1867478512⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 276) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 277) = ⟨1867478512, 1141568255⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 277 = 706741248 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_706741248

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1867478512, 1141568255⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 277) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 278) = ⟨1098427204, 880292698⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 278 = 438305792 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_438305792

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1098427204, 880292698⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 278) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 279) = ⟨880292698, 1049056443⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 279 = 975176704 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_975176704

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨880292698, 1049056443⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 279) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 280) = ⟨10571466, 1530894063⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 280 = 102761472 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_102761472

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨10571466, 1530894063⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 280) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 281) = ⟨1530894063, 2136912181⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 281 = 639632384 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_639632384

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1530894063, 2136912181⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 281) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 282) = ⟨1927076832, 605215390⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 282 = 371196928 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_371196928

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1927076832, 605215390⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 282) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 283) = ⟨605215390, 220406815⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 283 = 908067840 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_908067840

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨605215390, 220406815⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 283) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 284) = ⟨1461025413, 1421466600⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 284 = 236979200 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_236979200

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1461025413, 1421466600⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 284) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 285) = ⟨1421466600, 686458234⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 285 = 773850112 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_773850112

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1421466600, 686458234⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 285) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 286) = ⟨725035983, 816938404⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 286 = 505414656 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_505414656

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨725035983, 816938404⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 286) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 287) = ⟨816938404, 1422447664⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 287 = 1042285568 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1042285568

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨816938404, 1422447664⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 287) := by
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

end R17TableAChunk08Certificate
