import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableBChunk11Certificate
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

theorem power_33 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33 = ⟨1913739346, 534400073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35 = ⟨1596944750, 88648184⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37 = ⟨1116134331, 706674503⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38 = ⟨1101912995, 1017254605⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39 = ⟨1144034002, 1214860270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41 = ⟨2015439815, 1268983748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43 = ⟨1302319644, 1518526673⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45 = ⟨1184649672, 663036851⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46 = ⟨1969372712, 2106756523⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47 = ⟨250390235, 1321538300⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49 = ⟨173329971, 658630173⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51 = ⟨28745712, 1456833181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52 = ⟨601334839, 2077241415⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53 = ⟨229109997, 409681538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54 = ⟨315105149, 1708968384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55 = ⟨1031310599, 2131224704⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57 = ⟨1324336507, 1510176907⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58 = ⟨1487208781, 1372260843⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59 = ⟨329531323, 1831382818⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61 = ⟨1141618368, 506862428⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62 = ⟨440589667, 369146577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63 = ⟨620740300, 969723880⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_67 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67 = ⟨1982486292, 1611456260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_70 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70 = ⟨115184242, 829081638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71 = ⟨1729511182, 267661745⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_75 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 75 = ⟨682717731, 922798389⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77 = ⟨1255986648, 1483159588⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_78 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 78 = ⟨781174115, 499310652⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_79 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79 = ⟨1868709812, 514083020⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_83 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83 = ⟨1069733101, 25059729⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_86 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86 = ⟨1687815885, 1893568127⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87 = ⟨1648565317, 52537112⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90 = ⟨430426420, 308360131⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_91 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 91 = ⟨924358641, 1577205411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_93 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93 = ⟨1406255700, 949804171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94 = ⟨210531009, 2093722465⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_95 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 95 = ⟨1583351983, 982634748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_99 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 99 = ⟨1303248187, 75374765⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102 = ⟨1516486685, 2082671253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_103 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103 = ⟨2138693243, 755167780⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104 = ⟨595835346, 937999867⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_107 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 107 = ⟨1286380731, 398286559⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_109 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109 = ⟨584812917, 431696491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_110 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110 = ⟨1871453256, 445548378⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_111 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 111 = ⟨458549166, 1350497021⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115 = ⟨1772811593, 1752614228⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_116 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116 = ⟨894357328, 342875169⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_118 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118 = ⟨2029146254, 280154270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_119 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119 = ⟨2017000003, 1501730632⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122 = ⟨910427772, 437706403⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123 = ⟨830648882, 1820319682⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125 = ⟨228087554, 1931649501⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126 = ⟨647666107, 883025679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_127 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 127 = ⟨215093227, 1600453215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_134 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 134 = ⟨445214781, 1346295538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_141 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 141 = ⟨1089936147, 199619290⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_142 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 142 = ⟨2045471800, 21567742⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_150 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 150 = ⟨141696057, 732771971⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_154 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 154 = ⟨324269316, 652412893⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_157 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 157 = ⟨136913421, 2042158206⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_158 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 158 = ⟨489525484, 1281277745⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_166 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 166 = ⟨1545644833, 1423557268⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_173 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 173 = ⟨172481178, 435324837⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_174 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 174 = ⟨1566056996, 1745888105⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_180 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 180 = ⟨440283696, 1083008219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_182 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 182 = ⟨2049618010, 1067206337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_186 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 186 = ⟨522032805, 1817076066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_189 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 189 = ⟨1316098247, 562370549⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_190 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 190 = ⟨440498398, 1405716006⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_95]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_198 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 198 = ⟨1388304776, 536803269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_205 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 205 = ⟨1921054693, 699847975⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_206 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 206 = ⟨891793723, 1417325858⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 208 = ⟨1397719779, 1280626794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_214 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 214 = ⟨1649714937, 2053196164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_107]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_218 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 218 = ⟨720704015, 1704001039⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_221 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 221 = ⟨1818458494, 2013272533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_222 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 222 = ⟨727910565, 2105491058⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_230 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 230 = ⟨1382570788, 293157249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 232 = ⟨1705761383, 185122675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_237 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 237 = ⟨1434289749, 1293959886⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_238 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 238 = ⟨1707325511, 1098406816⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_244 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 244 = ⟨840379230, 2035177650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_246 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 246 = ⟨1542475593, 236234992⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_250 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 250 = ⟨1254622717, 393467164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_253 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 253 = ⟨1147263237, 1829594721⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_254 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 254 = ⟨1336163041, 934467179⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_127]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_269 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 269 = ⟨1172582534, 1842776856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_134]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_282 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 282 = ⟨1157625612, 1914432435⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_141]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_285 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 285 = ⟨1944626719, 1801694631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_142]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_301 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 301 = ⟨447030795, 673108803⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_150]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_308 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 308 = ⟨1275566012, 926001803⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_154]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_314 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 314 = ⟨2053983299, 121189260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_157]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_317 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 317 = ⟨1557700813, 1862842649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_158]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_333 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 333 = ⟨632550734, 664000417⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_166]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_346 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 346 = ⟨164892227, 1820409188⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_173]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_349 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 349 = ⟨333063580, 1384641728⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_174]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 360 = ⟨1022383927, 1626835633⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_180]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_365 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 365 = ⟨980841149, 1557362981⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_182]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_372 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 372 = ⟨1865434190, 2013555186⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_186]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_378 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 378 = ⟨1288817042, 187945461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_189]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_381 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 381 = ⟨716216549, 851808496⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_190]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_397 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 397 = ⟨808282204, 629874469⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_198]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_410 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 410 = ⟨1593040053, 504124593⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_205]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_413 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 413 = ⟨517977824, 650735201⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_206]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 416 = ⟨1719486678, 1121851154⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_429 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 429 = ⟨2077832894, 82591095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_214]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_436 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 436 = ⟨416123875, 1134162993⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_218]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_442 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 442 = ⟨969476270, 914192185⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_221]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_445 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 445 = ⟨1613462439, 1162512714⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_222]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_461 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 461 = ⟨1735228201, 2114702505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_230]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 464 = ⟨761225645, 1514363314⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_474 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 474 = ⟨1093702517, 1838031466⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_237]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_477 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 477 = ⟨563688045, 156476173⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_238]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 488 = ⟨1001236781, 1044516446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_244]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_493 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 493 = ⟨1148516555, 1503201764⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_246]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_500 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 500 = ⟨373864208, 678267884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_250]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_506 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 506 = ⟨1956083444, 203253931⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_253]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_509 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 509 = ⟨1730947292, 1177659995⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_254]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_538 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 538 = ⟨874005122, 460688045⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_269]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_564 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 564 = ⟨990133713, 890342639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_282]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_570 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 570 = ⟨233034296, 1384521359⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_285]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_602 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 602 = ⟨583164418, 443554023⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_301]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 616 = ⟨1723903332, 1162738935⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_308]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_628 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 628 = ⟨834478202, 563444626⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_314]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_634 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 634 = ⟨882078686, 781979785⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_317]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_666 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 666 = ⟨444257581, 1162367478⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_333]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_692 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 692 = ⟨755576242, 883344195⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_346]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_698 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 698 = ⟨2090163203, 1393260098⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_349]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 720 = ⟨330499511, 1255545984⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_730 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 730 = ⟨1891191359, 789399230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_365]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 744 = ⟨1746837725, 1648052895⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_372]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_756 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 756 = ⟨980032749, 2118809416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_378]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_762 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 762 = ⟨282798504, 493882647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_381]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_794 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 794 = ⟨1510604512, 1955687677⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_397]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_820 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 820 = ⟨1621830008, 530224415⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_410]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_826 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 826 = ⟨1219187057, 1697060398⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_413]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 832 = ⟨529167155, 49384636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_858 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 858 = ⟨1263220138, 266218491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_429]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 872 = ⟨1436111776, 1927355740⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_436]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_884 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 884 = ⟨1866152823, 884377881⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_442]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_890 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 890 = ⟨472538722, 237444208⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_445]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_922 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 922 = ⟨1534720214, 1208913963⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_461]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 928 = ⟨192925011, 1863974752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_948 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 948 = ⟨1476786005, 180925149⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_474]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_954 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 954 = ⟨1712648070, 1633247343⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_477]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 976 = ⟨1625484020, 323681644⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_986 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 986 = ⟨1287473258, 307612618⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_493]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1000 = ⟨2140279415, 2123398265⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_500]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1012 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1012 = ⟨715269835, 1012474773⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_506]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1018 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1018 = ⟨1520253980, 1695127944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_509]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1076 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1076 = ⟨1572211020, 1571550461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_538]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1128 = ⟨1565940610, 1178187397⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_564]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1140 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1140 = ⟨1524863199, 1850932105⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_570]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1204 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1204 = ⟨66840204, 1699289374⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_602]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1232 = ⟨467208929, 1117284316⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1256 = ⟨2133671141, 1426847807⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_628]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1268 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1268 = ⟨368793865, 1495790563⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_634]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1332 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1332 = ⟨331648197, 1727170153⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_666]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1384 = ⟨1158220058, 1179641218⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_692]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1396 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1396 = ⟨1000632623, 1774205120⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_698]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1440 = ⟨1445302729, 1296213244⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1460 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1460 = ⟨1337430864, 652877383⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_730]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1488 = ⟨2066061064, 79229564⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1512 = ⟨1818389294, 2061335507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_756]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1524 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1524 = ⟨484376532, 1415405067⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_762]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1588 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1588 = ⟨1370400357, 1150123185⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_794]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1640 = ⟨1813157545, 1272324159⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_820]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1652 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1652 = ⟨1077979543, 2094624439⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_826]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1664 = ⟨288424812, 1959942454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1716 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1716 = ⟨172771312, 2063947919⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_858]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1744 = ⟨329186677, 1544326724⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1768 = ⟨312856505, 1611160134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_884]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1780 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1780 = ⟨575498665, 1775141050⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_890]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1844 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1844 = ⟨588671453, 1901093011⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_922]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1856 = ⟨2162587, 1662102570⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1896 = ⟨161393962, 1843672076⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_948]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1908 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1908 = ⟨1290385052, 1816035369⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_954]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1952 = ⟨1871828618, 1847683492⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1972 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1972 = ⟨1040405395, 1609465700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_986]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2000 = ⟨1147858255, 2118048⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2024 = ⟨302004144, 1085673438⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1012]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2036 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2036 = ⟨1899364729, 435097626⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1018]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2152 = ⟨1778642409, 1748471508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1076]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2256 = ⟨674941568, 69635140⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2280 = ⟨335443230, 355422839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1140]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2408 = ⟨1552889395, 473396616⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1204]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2464 = ⟨1542370492, 267773083⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2512 = ⟨1454633817, 887981738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2536 = ⟨1757893165, 673463477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1268]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2664 = ⟨943402597, 987356844⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1332]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2768 = ⟨449129006, 1767494420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2792 = ⟨2014962804, 523977320⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1396]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2880 = ⟨2050207099, 979596272⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2920 = ⟨93664317, 2098401984⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1460]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2976 = ⟨1338602267, 1116448727⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3024 = ⟨1337702812, 1924764593⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3048 = ⟨867579899, 1696627318⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1524]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3176 = ⟨1998993787, 1869878368⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1588]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3280 = ⟨2002499842, 1064027224⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3304 = ⟨942867108, 897961181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1652]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3328 = ⟨1399167609, 1906303117⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3432 = ⟨387330917, 1977144470⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1716]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3488 = ⟨1891426405, 1154799597⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3536 = ⟨1736202702, 541512649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3560 = ⟨1357824263, 685259032⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1780]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3688 = ⟨717397300, 493025199⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1844]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3712 = ⟨1273782452, 924138332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3792 = ⟨1399177187, 613275639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3816 = ⟨1893909833, 1864236685⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1908]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3904 = ⟨314388810, 1013513450⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3944 = ⟨1166786282, 466431157⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1972]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4000 = ⟨2079500206, 62336377⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4048 = ⟨491409746, 2136646148⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4072 = ⟨710883624, 1324705616⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2036]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4304 = ⟨2025554035, 691073148⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4512 = ⟨1571173152, 1297316795⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4560 = ⟨678946883, 221929715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4816 = ⟨113514651, 1517097203⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4928 = ⟨1851793512, 331539505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5024 = ⟨2030420441, 205413565⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5072 = ⟨70774696, 113193600⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5328 = ⟨1733603227, 1391235601⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5536 = ⟨514904628, 1852012252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5584 = ⟨913230925, 250162533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5760 = ⟨175645010, 1734378279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5840 = ⟨2010274065, 958268277⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5952 = ⟨533092340, 383019730⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6048 = ⟨1414219515, 455436027⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6096 = ⟨2014056503, 936158667⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6352 = ⟨1286225608, 1721547561⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6560 = ⟨819553148, 474842885⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6608 = ⟨1276600166, 699378494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6656 = ⟨1510720600, 1956487951⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6864 = ⟨330221653, 169234414⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6976 = ⟨950603389, 1193852273⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7072 = ⟨1836512819, 1311198424⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7120 = ⟨460814753, 506459635⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7376 = ⟨54747966, 954176464⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7424 = ⟨719349967, 2102971509⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7584 = ⟨1116836362, 1045930896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7632 = ⟨1626846117, 500327508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7808 = ⟨1996451271, 146269947⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7888 = ⟨1418387603, 506875811⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8000 = ⟨1034240275, 1347145792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8096 = ⟨1877060741, 1026508439⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8144 = ⟨1291007281, 374894486⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8608 = ⟨1420537429, 1431339003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9024 = ⟨947141678, 1574276826⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9120 = ⟨2073937419, 1452176471⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9632 = ⟨1747056932, 1424449696⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9856 = ⟨579818567, 708464220⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10048 = ⟨1935645027, 706163636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10144 = ⟨895314775, 246358203⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10656 = ⟨120558844, 1765184433⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11072 = ⟨1458201270, 987288878⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11168 = ⟨280581860, 1142478190⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11520 = ⟨1411573869, 756888130⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11680 = ⟨2048300242, 1363630064⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11904 = ⟨387321092, 162791576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12096 = ⟨881223439, 1652308299⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12192 = ⟨227219127, 1381685401⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12704 = ⟨1038160504, 619405131⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13120 = ⟨1124810688, 1033695992⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13216 = ⟨171525219, 1606962694⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13312 = ⟨721344225, 1097609337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13728 = ⟨581926071, 240590851⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13952 = ⟨1440836092, 1085471181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14144 = ⟨1590571023, 2015621643⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14240 = ⟨314104874, 1169270772⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14752 = ⟨436510281, 979686893⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14848 = ⟨520833839, 1618182004⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15168 = ⟨444881175, 526464189⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15264 = ⟨1607936593, 1892273782⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15616 = ⟨139198880, 1155184073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15776 = ⟨648602543, 962694359⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16000 = ⟨1030880657, 718864663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16192 = ⟨1538253922, 207486583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16288 = ⟨413917518, 766558792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17216 = ⟨948946586, 933147682⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18048 = ⟨561474802, 2081083045⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18240 = ⟨405405471, 1075428447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19264 = ⟨82613726, 1852799958⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19712 = ⟨1355473385, 1096376971⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20096 = ⟨448730779, 758625649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20288 = ⟨216985926, 578881361⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21312 = ⟨658979862, 856006048⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22144 = ⟨999880307, 529086317⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22336 = ⟨1785379403, 1181318536⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23040 = ⟨512700922, 986405252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23360 = ⟨236787681, 1325822696⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23808 = ⟨1929818386, 55540944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24192 = ⟨1971169145, 1140904454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24384 = ⟨140090658, 749692230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25408 = ⟨207508282, 429395782⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26240 = ⟨1526443891, 484288181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26432 = ⟨106403118, 1146653075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26624 = ⟨2056541252, 1900478857⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27456 = ⟨1219750738, 2138195832⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27904 = ⟨351222675, 1148291511⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28288 = ⟨1455654707, 1587959477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28480 = ⟨1223327635, 169460176⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29504 = ⟨1524638353, 817347275⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29696 = ⟨1800149012, 1373092732⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30336 = ⟨1617861171, 235619726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30528 = ⟨27194435, 512630185⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31232 = ⟨1863885482, 1326705008⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31552 = ⟨1069150031, 1140666310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32000 = ⟨424799909, 191617025⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32384 = ⟨1859092454, 2007264786⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32576 = ⟨1384062492, 721809883⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34432 = ⟨1715079122, 951656889⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36096 = ⟨1211248826, 185397697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36480 = ⟨360261223, 170039208⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38528 = ⟨846812757, 1519458456⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39424 = ⟨1008501773, 1237883647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40192 = ⟨2109702297, 438879942⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40576 = ⟨632739031, 132875666⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42624 = ⟨1152894027, 887770543⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44288 = ⟨1730274123, 949691994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44672 = ⟨72113926, 367874375⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46080 = ⟨2092093316, 989477899⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46720 = ⟨293941037, 200868187⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47616 = ⟨895473556, 561535522⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48384 = ⟨2132971880, 1836933420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48768 = ⟨88364490, 1364148447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50816 = ⟨1437678721, 2133363507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52480 = ⟨1087936139, 1292268408⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52864 = ⟨1225133146, 212231012⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53248 = ⟨528497962, 2048433423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54912 = ⟨1821251531, 1996681602⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55808 = ⟨193409102, 1106498791⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56576 = ⟨2077325575, 1506287972⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56960 = ⟨598824722, 61010233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59008 = ⟨1843338859, 1647084033⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59392 = ⟨1076514332, 1068664781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60672 = ⟨1387747854, 56474655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61056 = ⟨1670518140, 1448069731⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62464 = ⟨1733341057, 673759763⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63104 = ⟨54091796, 2035675474⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64000 = ⟨1137104901, 634195134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64768 = ⟨999288239, 1760438388⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65152 = ⟨284942275, 1220234706⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_68864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 68864 = ⟨1779662355, 1040313848⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72192 = ⟨894280518, 1968367347⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72960 = ⟨2037768553, 1561490030⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77056 = ⟨45935969, 134055077⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_78848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 78848 = ⟨912283038, 323725110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_80384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 80384 = ⟨350290493, 912098088⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_81152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81152 = ⟨126552455, 118944911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_85248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 85248 = ⟨1833069753, 155213654⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88576 = ⟨544822653, 2069348221⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89344 = ⟨2113195849, 622035143⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92160 = ⟨713314261, 425545952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_93440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93440 = ⟨330494473, 635368100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_95232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 95232 = ⟨658974643, 1874009431⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_96768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96768 = ⟨1090205761, 1327676402⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_97536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 97536 = ⟨680426789, 625965104⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_101632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101632 = ⟨941237643, 753151646⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104960 = ⟨132278529, 1557996220⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105728 = ⟨619899911, 1030634936⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_109824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109824 = ⟨385155513, 740659839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_111616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 111616 = ⟨1624655281, 300914040⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_113152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 113152 = ⟨282530609, 1669125882⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_113920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 113920 = ⟨1961516328, 1807210884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_118016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118016 = ⟨2091748070, 2146760702⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_118784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118784 = ⟨845078094, 149898124⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121344 = ⟨441161107, 456269102⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122112 = ⟨1902405641, 632602105⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124928 = ⟨346773666, 152947344⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126208 = ⟨1243060112, 1393296081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_128000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128000 = ⟨1070571079, 1366506169⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_129536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 129536 = ⟨1473092905, 2009177526⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_130304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 130304 = ⟨1550871604, 201685568⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_137728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 137728 = ⟨295830113, 874481580⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_144384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 144384 = ⟨1692492513, 693418291⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_145920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 145920 = ⟨191500183, 192251932⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_154112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 154112 = ⟨222788109, 1550289287⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_157696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 157696 = ⟨611826819, 1330717448⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_160768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 160768 = ⟨1968029066, 1017740468⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_162304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 162304 = ⟨1993155203, 2106058362⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_170496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 170496 = ⟨1235731113, 597530308⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_177152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 177152 = ⟨1776728469, 999929976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_178688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 178688 = ⟨568473543, 1236348275⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_184320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 184320 = ⟨1029245122, 1158447597⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_186880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 186880 = ⟨616709292, 2082681563⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_190464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 190464 = ⟨1124013519, 1413144457⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_95232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_193536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 193536 = ⟨2040482720, 1052946078⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_195072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 195072 = ⟨1579526235, 1362909765⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_97536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_203264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 203264 = ⟨480821075, 1958103910⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_209920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 209920 = ⟨1050954735, 1201222275⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_211456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 211456 = ⟨856077301, 824823342⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_219648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 219648 = ⟨947260033, 1683924206⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_223232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 223232 = ⟨1078945591, 1940049095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_226304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 226304 = ⟨1072364318, 265089706⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_113152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_227840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 227840 = ⟨866195563, 1200984190⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_113920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_236032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 236032 = ⟨525590040, 1042091208⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_242688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 242688 = ⟨970631068, 228952312⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_244224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 244224 = ⟨260427144, 6681250⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_249856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 249856 = ⟨887385898, 608769478⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_252416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 252416 = ⟨16578863, 1317550430⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_256000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 256000 = ⟨1425723522, 1087018637⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_259072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 259072 = ⟨1556101373, 1161670897⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_129536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_260608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 260608 = ⟨2080100784, 180135845⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_130304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_275456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 275456 = ⟨1315896544, 437244449⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_137728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_288768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 288768 = ⟨443122237, 696551100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_144384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_291840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 291840 = ⟨1241987904, 1809123808⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_145920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_308224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 308224 = ⟨26092218, 598138554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_154112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_315392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 315392 = ⟨1576856103, 1461690978⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_157696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_321536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 321536 = ⟨1102231607, 609468827⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_160768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_324608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 324608 = ⟨2037456598, 313996494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_162304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_340992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 340992 = ⟨835293937, 54999625⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_170496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_354304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 354304 = ⟨533049899, 1473067927⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_177152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_357376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 357376 = ⟨1022796416, 1057744923⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_178688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_373760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 373760 = ⟨1530853600, 1113295684⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_186880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_380928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 380928 = ⟨647843950, 788293466⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_190464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_387072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 387072 = ⟨1968056945, 1093869942⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_193536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_390144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 390144 = ⟨1686754661, 852831802⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_195072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_406528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 406528 = ⟨883904040, 752522382⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_203264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_419840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 419840 = ⟨114019110, 1704020237⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_209920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_422912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 422912 = ⟨1084735603, 900951681⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_211456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_439296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 439296 = ⟨1887704601, 272154406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_219648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_446464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 446464 = ⟨2076036242, 130048956⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_223232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_452608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 452608 = ⟨1512942634, 1920073229⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_226304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_455680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 455680 = ⟨1601883610, 240764936⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_227840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_472064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 472064 = ⟨936440205, 1605680361⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_236032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_485376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 485376 = ⟨1797665716, 1562938324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_242688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_488448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 488448 = ⟨1282015379, 1263925793⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_244224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_504832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 504832 = ⟨237819183, 1206146729⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_252416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_512000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 512000 = ⟨1615674956, 1808914239⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_256000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_518144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 518144 = ⟨1187658047, 1597100399⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_259072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_521216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 521216 = ⟨1710325456, 763149856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_260608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_550912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 550912 = ⟨1957875930, 296561667⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_275456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_577536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 577536 = ⟨58617043, 693726782⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_288768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_583680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 583680 = ⟨1812847060, 604811917⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_291840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_616448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 616448 = ⟨2116389638, 752539481⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_308224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_643072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 643072 = ⟨25637092, 421692094⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_321536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_649216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 649216 = ⟨2008431186, 940311739⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_324608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_681984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 681984 = ⟨1347334562, 1707466059⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_340992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_708608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 708608 = ⟨1210158521, 1506582976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_354304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_714752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 714752 = ⟨610182946, 362571378⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_357376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_747520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 747520 = ⟨2130500018, 697494463⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_373760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_774144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 774144 = ⟨852276839, 226974950⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_387072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_780288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 780288 = ⟨501634918, 1964085203⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_390144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_813056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 813056 = ⟨276270000, 635791752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_406528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_839680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 839680 = ⟨799756877, 308500462⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_419840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_845824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 845824 = ⟨247373802, 1199896598⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_422912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_878592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 878592 = ⟨489683669, 1738843794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_439296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_905216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 905216 = ⟨69829270, 1352453515⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_452608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_911360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 911360 = ⟨1494170122, 1749961689⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_455680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_944128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 944128 = ⟨784554145, 618566048⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_472064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_970752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 970752 = ⟨1797669071, 2141355836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_485376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_976896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 976896 = ⟨1588926912, 436478465⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_488448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1009664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1009664 = ⟨1048721901, 873552759⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_504832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1036288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1036288 = ⟨2126452532, 708823575⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_518144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1042432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1042432 = ⟨1732548992, 915469288⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_521216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1101824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1101824 = ⟨668998651, 249239603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_550912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1167360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1167360 = ⟨674296139, 317324829⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_583680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1232896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1232896 = ⟨1058730422, 1950344727⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_616448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1298432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1298432 = ⟨1269707845, 1452388824⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_649216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1363968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1363968 = ⟨1488450015, 601243945⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_681984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1429504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1429504 = ⟨148228362, 590602766⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_714752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1495040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1495040 = ⟨185991083, 1518281638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_747520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1560576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1560576 = ⟨406123904, 764760651⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_780288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1626112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1626112 = ⟨1475204899, 1648029352⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_813056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1691648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1691648 = ⟨970891652, 610465777⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_845824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1757184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1757184 = ⟨826608058, 2050139532⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_878592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1822720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1822720 = ⟨412577235, 1997534047⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_911360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1888256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1888256 = ⟨571821609, 1489087773⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_944128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1953792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1953792 = ⟨1683233817, 1287709593⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_976896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2019328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2019328 = ⟨413934600, 1586830163⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1009664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2084864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2084864 = ⟨1991612315, 1875574124⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1042432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 352) = ⟨528497962, 2048433423⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 352 = 53248 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_53248

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨528497962, 2048433423⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 352) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 353) = ⟨668998651, 249239603⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 353 = 1101824 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1101824

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨668998651, 249239603⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 353) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 354) = ⟨58617043, 693726782⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 354 = 577536 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_577536

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨58617043, 693726782⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 354) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 355) = ⟨1475204899, 1648029352⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 355 = 1626112 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1626112

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1475204899, 1648029352⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 355) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 356) = ⟨1576856103, 1461690978⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 356 = 315392 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_315392

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1576856103, 1461690978⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 356) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 357) = ⟨1488450015, 601243945⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 357 = 1363968 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1363968

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1488450015, 601243945⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 357) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 358) = ⟨799756877, 308500462⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 358 = 839680 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_839680

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨799756877, 308500462⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 358) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 359) = ⟨571821609, 1489087773⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 359 = 1888256 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1888256

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨571821609, 1489087773⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 359) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 360) = ⟨1029245122, 1158447597⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 360 = 184320 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_184320

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1029245122, 1158447597⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 360) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 361) = ⟨1058730422, 1950344727⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 361 = 1232896 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1232896

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1058730422, 1950344727⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 361) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 362) = ⟨1210158521, 1506582976⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 362 = 708608 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_708608

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1210158521, 1506582976⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 362) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 363) = ⟨826608058, 2050139532⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 363 = 1757184 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1757184

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨826608058, 2050139532⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 363) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 364) = ⟨2076036242, 130048956⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 364 = 446464 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_446464

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2076036242, 130048956⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 364) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 365) = ⟨185991083, 1518281638⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 365 = 1495040 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1495040

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨185991083, 1518281638⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 365) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 366) = ⟨1797669071, 2141355836⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 366 = 970752 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_970752

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1797669071, 2141355836⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 366) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 367) = ⟨413934600, 1586830163⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 367 = 2019328 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2019328

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨413934600, 1586830163⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 367) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 368) = ⟨845078094, 149898124⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 368 = 118784 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_118784

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨845078094, 149898124⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 368) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 369) = ⟨674296139, 317324829⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 369 = 1167360 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1167360

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨674296139, 317324829⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 369) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 370) = ⟨25637092, 421692094⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 370 = 643072 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_643072

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨25637092, 421692094⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 370) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 371) = ⟨970891652, 610465777⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 371 = 1691648 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1691648

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨970891652, 610465777⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 371) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 372) = ⟨647843950, 788293466⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 372 = 380928 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_380928

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨647843950, 788293466⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 372) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 373) = ⟨148228362, 590602766⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 373 = 1429504 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1429504

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨148228362, 590602766⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 373) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 374) = ⟨69829270, 1352453515⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 374 = 905216 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_905216

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨69829270, 1352453515⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 374) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 375) = ⟨1683233817, 1287709593⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 375 = 1953792 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1953792

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1683233817, 1287709593⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 375) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 376) = ⟨887385898, 608769478⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 376 = 249856 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_249856

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨887385898, 608769478⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 376) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 377) = ⟨1269707845, 1452388824⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 377 = 1298432 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1298432

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1269707845, 1452388824⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 377) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 378) = ⟨852276839, 226974950⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 378 = 774144 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_774144

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨852276839, 226974950⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 378) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 379) = ⟨412577235, 1997534047⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 379 = 1822720 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1822720

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨412577235, 1997534047⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 379) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 380) = ⟨1615674956, 1808914239⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 380 = 512000 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_512000

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1615674956, 1808914239⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 380) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 381) = ⟨406123904, 764760651⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 381 = 1560576 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1560576

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨406123904, 764760651⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 381) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 382) = ⟨2126452532, 708823575⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 382 = 1036288 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1036288

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2126452532, 708823575⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 382) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 383) = ⟨1991612315, 1875574124⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 383 = 2084864 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2084864

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1991612315, 1875574124⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 383) := by
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

end R17TableBChunk11Certificate
