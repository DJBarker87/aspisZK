import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk11Certificate
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

theorem power_26625 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26625 = ⟨1518933700, 1724677146⟩ := by
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

theorem power_53250 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53250 = ⟨1605321164, 1001537696⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26625]
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

theorem power_59393 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59393 = ⟨895863601, 9412385⟩ := by
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

theorem power_92161 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92161 = ⟨2067010757, 237380672⟩ := by
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

theorem power_106500 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106500 = ⟨1789960289, 484986806⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53250]
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

theorem power_118786 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118786 = ⟨745453874, 937104600⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59393]
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

theorem power_124929 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124929 = ⟨59755461, 726252122⟩ := by
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

theorem power_157697 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 157697 = ⟨590937771, 352372152⟩ := by
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

theorem power_184322 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 184322 = ⟨1822103913, 295345088⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92161]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_186880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 186880 = ⟨616709292, 2082681563⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_190465 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 190465 = ⟨1757781165, 295171671⟩ := by
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

theorem power_213000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 213000 = ⟨764265527, 1310749501⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106500]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_219648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 219648 = ⟨947260033, 1683924206⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_223233 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 223233 = ⟨151211398, 1662348733⟩ := by
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

theorem power_237572 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 237572 = ⟨1488689594, 1176212705⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118786]
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

theorem power_249858 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 249858 = ⟨1287833952, 1542996431⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124929]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_252416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 252416 = ⟨16578863, 1317550430⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_256001 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 256001 = ⟨388922770, 1083247200⟩ := by
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

theorem power_288769 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 288769 = ⟨211521741, 461253412⟩ := by
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

theorem power_315394 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 315394 = ⟨1739724221, 1936745520⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_157697]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_321537 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 321537 = ⟨1144027157, 231211927⟩ := by
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

theorem power_354305 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 354305 = ⟨845643606, 1246283189⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_177152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_357376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 357376 = ⟨1022796416, 1057744923⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_178688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_368644 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 368644 = ⟨2007254979, 1537135554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_184322]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_373760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 373760 = ⟨1530853600, 1113295684⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_186880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_380930 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 380930 = ⟨1338980654, 1783643319⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_190465]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_387073 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 387073 = ⟨1302883104, 1293577255⟩ := by
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

theorem power_419841 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 419841 = ⟨113189661, 895842603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_209920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_422912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 422912 = ⟨1084735603, 900951681⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_211456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_426000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 426000 = ⟨1113660821, 1563741249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_213000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_439296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 439296 = ⟨1887704601, 272154406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_219648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_446466 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 446466 = ⟨713077312, 148157521⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_223233]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_452609 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 452609 = ⟨1240994792, 1302296604⟩ := by
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

theorem power_475144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 475144 = ⟨522044143, 1777514150⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_237572]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_485377 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 485377 = ⟨1827883554, 678198735⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_242688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_488448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 488448 = ⟨1282015379, 1263925793⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_244224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_499716 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 499716 = ⟨65058587, 1704141135⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_249858]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_504832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 504832 = ⟨237819183, 1206146729⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_252416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_512002 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 512002 = ⟨1015372429, 1534368808⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_256001]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_518145 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 518145 = ⟨455508463, 88872911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_259072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_521216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 521216 = ⟨1710325456, 763149856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_260608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_550913 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 550913 = ⟨673816743, 1792368388⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_275456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_577538 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 577538 = ⟨1187403968, 463213443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_288769]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_583681 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 583681 = ⟨2115370507, 1721856741⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_291840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_616449 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 616449 = ⟨526089561, 446780326⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_308224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_630788 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 630788 = ⟨1297891475, 304998379⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_315394]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_643074 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 643074 = ⟨420382547, 1702697588⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_321537]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_649217 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 649217 = ⟨427489337, 59560753⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_324608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_681985 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 681985 = ⟨639013610, 1688799384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_340992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_708610 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 708610 = ⟨1153908764, 590702332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_354305]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_714753 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 714753 = ⟨1864686189, 871046436⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_357376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_737288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 737288 = ⟨2140409247, 88257796⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_368644]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_747521 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 747521 = ⟨1637432141, 1779028893⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_373760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_761860 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 761860 = ⟨903429287, 375690551⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_380930]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_774146 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 774146 = ⟨1810007287, 599938122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_387073]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_780289 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 780289 = ⟨1339419494, 274913883⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_390144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_813057 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 813057 = ⟨1503218095, 1870702886⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_406528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_839682 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 839682 = ⟨216265724, 803877179⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_419841]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_845825 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 845825 = ⟨1454491699, 467595732⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_422912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_852000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 852000 = ⟨1233326546, 598368104⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_426000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_878593 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 878593 = ⟨25786247, 885741739⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_439296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_892932 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 892932 = ⟨343149758, 536356054⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_446466]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_905218 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 905218 = ⟨462828419, 1691656662⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_452609]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_911361 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 911361 = ⟨2132569467, 1251450119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_455680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_944129 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 944129 = ⟨1227747904, 956776960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_472064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_950288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 950288 = ⟨1347098863, 2032367386⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_475144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_970754 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 970754 = ⟨1031802898, 962057738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_485377]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_976897 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 976897 = ⟨481366198, 697113163⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_488448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_999432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 999432 = ⟨682319839, 1896842185⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_499716]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1009665 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1009665 = ⟨1889702529, 733998485⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_504832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1024004 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1024004 = ⟨1447953142, 340526640⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_512002]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1036290 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1036290 = ⟨156372750, 1371954300⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_518145]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1042433 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1042433 = ⟨813697391, 460878512⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_521216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1101826 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1101826 = ⟨768769477, 192532344⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_550913]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1155076 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1155076 = ⟨500000985, 682859261⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_577538]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1167362 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1167362 = ⟨1949714636, 1101097534⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_583681]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1232898 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1232898 = ⟨1621702168, 1223457659⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_616449]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1261576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1261576 = ⟨761669933, 2039433021⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_630788]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1286148 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1286148 = ⟨520660694, 1970366338⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_643074]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1298434 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1298434 = ⟨1546254227, 1275252872⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_649217]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1363970 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1363970 = ⟨800739891, 685306919⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_681985]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1417220 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1417220 = ⟨18209454, 147513821⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_708610]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1429506 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1429506 = ⟨521113525, 1747045540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_714753]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1474576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1474576 = ⟨57933329, 509332877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_737288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1495042 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1495042 = ⟨677582067, 1590849771⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_747521]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1523720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1523720 = ⟨1011357621, 759284630⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_761860]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1548292 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1548292 = ⟨1010031352, 1390046268⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_774146]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1560578 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1560578 = ⟨1811399025, 629661008⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_780289]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1626114 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1626114 = ⟨708202325, 165996834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_813057]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1679364 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1679364 = ⟨1970890631, 1322221747⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_839682]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1691650 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1691650 = ⟨1671113780, 1905826608⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_845825]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1704000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1704000 = ⟨1489186203, 1100461596⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_852000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1757186 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1757186 = ⟨1755514209, 2033258911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_878593]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1785864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1785864 = ⟨3019884, 334643531⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_892932]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1810436 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1810436 = ⟨531039753, 1616329933⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_905218]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1822722 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1822722 = ⟨1407766867, 689363011⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_911361]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1888258 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1888258 = ⟨1931940253, 832452671⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_944129]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1900576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1900576 = ⟨1638626485, 2009316398⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_950288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1941508 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1941508 = ⟨152936810, 271961980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_970754]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1953794 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1953794 = ⟨1717787462, 239170363⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_976897]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1998864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1998864 = ⟨1769638716, 590690141⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_999432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2019330 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2019330 = ⟨74540989, 1610507750⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1009665]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2048008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2048008 = ⟨541298644, 1389595176⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1024004]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2072580 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2072580 = ⟨1158727417, 870409204⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1036290]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2084866 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2084866 = ⟨1131612813, 257236886⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1042433]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2203652 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2203652 = ⟨1321904216, 925622990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1101826]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2310152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2310152 = ⟨248957482, 210785567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1155076]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2334724 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2334724 = ⟨680246031, 1582853689⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1167362]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2465796 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2465796 = ⟨3778090, 653824610⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1232898]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2523152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2523152 = ⟨1898655947, 772234776⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1261576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2572296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2572296 = ⟨1799411857, 417887183⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1286148]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2596868 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2596868 = ⟨1304346653, 849858507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1298434]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2727940 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2727940 = ⟨815346554, 2080145874⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1363970]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2834440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2834440 = ⟨1857442514, 1155504272⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1417220]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2859012 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2859012 = ⟨181830385, 1747732677⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1429506]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2949152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2949152 = ⟨1258761291, 812018646⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1474576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2990084 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2990084 = ⟨1691234533, 1723820357⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1495042]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3047440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3047440 = ⟨415992218, 1327769656⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1523720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3096584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3096584 = ⟨752354580, 358599488⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1548292]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3121156 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3121156 = ⟨1452758447, 760508524⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1560578]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3252228 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3252228 = ⟨79338151, 1657039610⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1626114]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3358728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3358728 = ⟨848862004, 1883807197⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1679364]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3383300 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3383300 = ⟨674848283, 1480787868⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1691650]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3408000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3408000 = ⟨530499670, 1297940811⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1704000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3514372 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3514372 = ⟨2119781948, 679346250⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1757186]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3571728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3571728 = ⟨820132940, 631057348⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1785864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3620872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3620872 = ⟨728521309, 102207638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1810436]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3645444 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3645444 = ⟨892628913, 322747165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1822722]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3776516 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3776516 = ⟨692646840, 1979839081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1888258]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3801152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3801152 = ⟨655529227, 898321315⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1900576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3883016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3883016 = ⟨1491165924, 1475403041⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1941508]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3907588 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3907588 = ⟨623573878, 237463421⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1953794]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3997728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3997728 = ⟨531328929, 331065975⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1998864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4038660 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4038660 = ⟨1310079227, 525830335⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2019330]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4096016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4096016 = ⟨1137763909, 2103883499⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2048008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4145160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4145160 = ⟨840199632, 1368291855⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2072580]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4169732 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4169732 = ⟨1498435634, 2133405640⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2084866]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4407304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4407304 = ⟨1411889294, 1088322990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2203652]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4620304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4620304 = ⟨1865246483, 477009687⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2310152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4669448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4669448 = ⟨1335996582, 2098164065⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2334724]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4931592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4931592 = ⟨1427976628, 1462647480⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2465796]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5046304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5046304 = ⟨253371237, 1617710141⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2523152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5144592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5144592 = ⟨522656283, 368991961⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2572296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5193736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5193736 = ⟨954219870, 2123527229⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2596868]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5455880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5455880 = ⟨1229121592, 328176870⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2727940]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5668880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5668880 = ⟨1783311521, 1618415474⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2834440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5718024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5718024 = ⟨94447017, 1011428222⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2859012]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5898304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5898304 = ⟨595365007, 327561846⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2949152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5980168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5980168 = ⟨1653361352, 248402057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2990084]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6094880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6094880 = ⟨1375702984, 1376097100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3047440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6193168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6193168 = ⟨52392765, 534921916⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3096584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6242312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6242312 = ⟨2137487200, 2027295394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3121156]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6504456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6504456 = ⟨546055498, 2005703260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3252228]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6717456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6717456 = ⟨531620739, 803092447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3358728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6766600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6766600 = ⟨243504831, 850079012⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3383300]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6816000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6816000 = ⟨92034506, 894372554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3408000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7028744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7028744 = ⟨347167947, 513919994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3514372]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7143456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7143456 = ⟨773711691, 1688253349⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3571728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7241744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7241744 = ⟨1446075503, 1702537854⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3620872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7290888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7290888 = ⟨1635841204, 1510207992⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3645444]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7553032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7553032 = ⟨2041541610, 506433487⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3776516]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7602304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7602304 = ⟨1685997563, 765504504⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3801152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7766032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7766032 = ⟨1902485454, 1819937153⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3883016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7815176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7815176 = ⟨1090978917, 1887358600⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3907588]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7995456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7995456 = ⟨791799262, 647847446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3997728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8077320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8077320 = ⟨1995161292, 1284196145⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4038660]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8192032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8192032 = ⟨39594286, 1858975535⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4096016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8290320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8290320 = ⟨1449493529, 161510962⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4145160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8339464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8339464 = ⟨1969379163, 141067110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4169732]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8814608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8814608 = ⟨1330199203, 466474145⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4407304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9240608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9240608 = ⟨25048210, 2004412674⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4620304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9338896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9338896 = ⟨544611296, 25783753⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4669448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9863184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9863184 = ⟨437151351, 1025387876⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4931592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10092608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10092608 = ⟨442619637, 1802606930⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5046304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10289184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10289184 = ⟨284227295, 1304345521⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5144592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10387472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10387472 = ⟨1492605465, 1244532342⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5193736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10911760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10911760 = ⟨1390936113, 1437482369⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5455880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11337760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11337760 = ⟨885315236, 1477647812⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5668880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11436048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11436048 = ⟨2092390084, 1693932364⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5718024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11796608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11796608 = ⟨924228575, 1212207695⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5898304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11960336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11960336 = ⟨418337036, 2039572990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5980168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12189760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12189760 = ⟨191953137, 1438884776⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6094880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12386336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12386336 = ⟨359840595, 215940026⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6193168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12484624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12484624 = ⟨192155915, 1355332708⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6242312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13008912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13008912 = ⟨759843572, 1398008727⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6504456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13434912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13434912 = ⟨843543003, 286775573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6717456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13533200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13533200 = ⟨197617027, 1655253840⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6766600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13632000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13632000 = ⟨962061755, 2049501241⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6816000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14057488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14057488 = ⟨1533138805, 147890716⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7028744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14286912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14286912 = ⟨2032659045, 1111592520⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7143456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14483488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14483488 = ⟨600882878, 533824217⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7241744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14581776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14581776 = ⟨542844600, 200302477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7290888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15106064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15106064 = ⟨741176084, 1854770440⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7553032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15204608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15204608 = ⟨745405006, 1748622503⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7602304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15532064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15532064 = ⟨2038862133, 1311982040⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7766032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15630352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15630352 = ⟨1363468643, 138434219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7815176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15990912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15990912 = ⟨1167280524, 942159469⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7995456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16154640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16154640 = ⟨779065616, 701952246⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8077320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16384064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16384064 = ⟨796250064, 544792480⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8192032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16580640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16580640 = ⟨208210155, 1135446448⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8290320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16678928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16678928 = ⟨843193139, 1763752509⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8339464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17629216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17629216 = ⟨318874654, 1891212220⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8814608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18481216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18481216 = ⟨1561342218, 1230246425⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9240608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18677792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18677792 = ⟨2072575445, 599528114⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9338896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19726368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19726368 = ⟨514444575, 1040967132⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9863184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20185216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20185216 = ⟨1194402090, 405993033⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10092608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20578368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20578368 = ⟨1692316463, 595038318⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10289184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20774944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20774944 = ⟨1402151074, 1308348700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10387472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21823520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21823520 = ⟨1694882880, 1501651472⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10911760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22675520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22675520 = ⟨699362383, 1258306876⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11337760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22872096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22872096 = ⟨105449869, 931354991⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11436048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23593216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23593216 = ⟨635599973, 895437471⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11796608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23920672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23920672 = ⟨1708666057, 576047242⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11960336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24379520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24379520 = ⟨2012431038, 969188968⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12189760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24772672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24772672 = ⟨19714669, 1448162321⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12386336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24969248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24969248 = ⟨1279370570, 2069527121⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12484624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26017824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26017824 = ⟨101761220, 1617960989⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13008912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26869824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26869824 = ⟨1941574744, 2005248611⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13434912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27066400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27066400 = ⟨2046835249, 1037560273⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13533200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27264000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27264000 = ⟨635778846, 1298887220⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13632000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28114976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28114976 = ⟨1450854714, 1288525306⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14057488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28573824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28573824 = ⟨1545641701, 120793196⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14286912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28966976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28966976 = ⟨29893505, 1101443432⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14483488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29163552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29163552 = ⟨699527433, 976119671⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14581776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30212128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30212128 = ⟨805605793, 334695558⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15106064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30409216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30409216 = ⟨1965610158, 482968484⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15204608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31064128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31064128 = ⟨1182013940, 611141804⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15532064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31260704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31260704 = ⟨960560438, 1164832093⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15630352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31981824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31981824 = ⟨1400189611, 1530939595⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15990912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32309280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32309280 = ⟨1350135966, 580099275⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16154640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32768128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32768128 = ⟨483783703, 2120527522⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16384064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33161280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33161280 = ⟨882057002, 414541077⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16580640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33357856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33357856 = ⟨299312921, 2018851387⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16678928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35258432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35258432 = ⟨1351213187, 2080071234⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17629216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36962432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36962432 = ⟨1687993189, 1094693749⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18481216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37355584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37355584 = ⟨644946776, 1644487044⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18677792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39452736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39452736 = ⟨88229456, 1060517198⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19726368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40370432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40370432 = ⟨1408294163, 1964293819⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20185216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41156736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41156736 = ⟨349731874, 1619990553⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20578368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41549888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41549888 = ⟨26000358, 1526300872⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20774944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43647040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43647040 = ⟨1332912051, 589621476⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21823520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45351040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45351040 = ⟨986719323, 514991575⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22675520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45744192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45744192 = ⟨505967733, 498859203⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22872096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47186432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47186432 = ⟨939065605, 1137631446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23593216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47841344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47841344 = ⟨203199275, 1797763769⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23920672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48759040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48759040 = ⟨889538266, 728357552⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24379520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49545344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49545344 = ⟨954436296, 1140847339⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24772672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49938496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49938496 = ⟨1869946540, 974592141⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24969248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52035648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52035648 = ⟨870339750, 1151364586⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26017824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53739648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53739648 = ⟨339645091, 1887456432⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26869824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54132800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54132800 = ⟨1795512477, 746456052⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27066400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56229952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56229952 = ⟨625856699, 975320092⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28114976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57147648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57147648 = ⟨1818020644, 1288230599⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28573824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57933952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57933952 = ⟨17154299, 1121264363⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28966976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58327104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58327104 = ⟨1106366513, 1283904027⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29163552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60424256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60424256 = ⟨600205638, 520962694⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30212128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60818432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60818432 = ⟨1016770609, 602494260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30409216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62128256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62128256 = ⟨1024584835, 1551744053⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31064128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62521408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62521408 = ⟨1981780941, 1747344705⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31260704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63963648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63963648 = ⟨1702841978, 652018525⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31981824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64618560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64618560 = ⟨855491329, 449268350⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32309280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65536256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65536256 = ⟨1258403061, 1703069349⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32768128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66322560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66322560 = ⟨1732168350, 1013608369⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33161280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66715712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66715712 = ⟨216424689, 1057522896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33357856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_70516864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70516864 = ⟨1200676961, 115295843⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35258432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73924864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73924864 = ⟨1186247969, 295426828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36962432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_74711168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 74711168 = ⟨609121500, 1817510693⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37355584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_78905472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 78905472 = ⟨1770934684, 879864387⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39452736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_80740864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 80740864 = ⟨388753080, 747812695⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40370432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_82313472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 82313472 = ⟨300684003, 1996354661⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41156736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_83099776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83099776 = ⟨855457950, 1735100996⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41549888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87294080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87294080 = ⟨347567582, 1301899202⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43647040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90702080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90702080 = ⟨1612666754, 1927325071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45351040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_91488384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 91488384 = ⟨424313265, 1238936658⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45744192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94372864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94372864 = ⟨1953093309, 1399852939⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47186432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_95682688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 95682688 = ⟨508532323, 458606958⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47841344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_97518080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 97518080 = ⟨1680646415, 1656221998⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48759040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_99090688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 99090688 = ⟨107598939, 184853252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49545344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_99876992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 99876992 = ⟨736403417, 349595165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49938496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104071296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104071296 = ⟨1862750336, 357597012⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52035648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_107479296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 107479296 = ⟨743178340, 1672511012⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53739648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108265600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108265600 = ⟨1485996369, 523698007⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54132800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_112459904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112459904 = ⟨656091430, 358618568⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56229952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_114295296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114295296 = ⟨1033760324, 1713782997⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57147648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115867904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115867904 = ⟨580065981, 1989300105⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57933952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_116654208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116654208 = ⟨1393955659, 2092458073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58327104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120848512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120848512 = ⟨1663330439, 2020987330⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60424256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124256512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124256512 = ⟨504743408, 352064724⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62128256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125042816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125042816 = ⟨335193323, 511844134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62521408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_127927296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 127927296 = ⟨321646901, 781973549⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63963648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_129237120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 129237120 = ⟨2041150174, 1533831320⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64618560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_131072512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131072512 = ⟨1200547099, 1709847979⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65536256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_132645120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 132645120 = ⟨2019151055, 1960297630⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66322560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_133431424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 133431424 = ⟨1578952548, 1142591134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66715712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_141033728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 141033728 = ⟨1335526221, 292542354⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70516864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_147849728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 147849728 = ⟨1396483830, 440508635⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73924864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_149422336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 149422336 = ⟨728292804, 1291292359⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74711168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_157810944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 157810944 = ⟨1681942114, 119079440⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78905472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_161481728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 161481728 = ⟨1273099376, 2109025845⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80740864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_164626944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 164626944 = ⟨2027830116, 1648885659⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82313472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_166199552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 166199552 = ⟨701915681, 447606143⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83099776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_174588160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 174588160 = ⟨1510346904, 258058867⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87294080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_181404160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 181404160 = ⟨791237095, 1641714038⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90702080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_182976768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 182976768 = ⟨638469328, 1004505312⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91488384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_191365376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 191365376 = ⟨1228887174, 1396500383⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_95682688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_195036160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 195036160 = ⟨298013744, 1631477536⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_97518080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_198181376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 198181376 = ⟨1312700289, 1840065610⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99090688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_199753984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 199753984 = ⟨650703713, 1447272348⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99876992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_208142592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 208142592 = ⟨1094574098, 329638003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104071296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_214958592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 214958592 = ⟨1432955113, 1816282378⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_107479296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_216531200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 216531200 = ⟨1577167423, 1754420910⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108265600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_224919808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 224919808 = ⟨690456820, 885008109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112459904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_228590592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 228590592 = ⟨1168611337, 1316554005⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114295296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_231735808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 231735808 = ⟨1784642968, 1200982051⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115867904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_233308416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 233308416 = ⟨1418574233, 1502333972⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116654208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_241697024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 241697024 = ⟨249603706, 198943257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120848512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_248513024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 248513024 = ⟨855307000, 1968874208⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124256512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_250085632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 250085632 = ⟨1420855030, 1049361386⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125042816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_258474240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 258474240 = ⟨124734062, 1513183016⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_129237120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_262145024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 262145024 = ⟨838659345, 1494392856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131072512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_265290240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 265290240 = ⟨434265291, 132139557⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_132645120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_266862848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 266862848 = ⟨1215312611, 1087787713⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133431424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_282067456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 282067456 = ⟨1727705984, 20922577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_141033728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_295699456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 295699456 = ⟨1420391248, 495658886⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_147849728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_298844672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 298844672 = ⟨740921842, 1467656096⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_149422336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_315621888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 315621888 = ⟨1894644679, 1877511125⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_157810944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_329253888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 329253888 = ⟨45277316, 1384212302⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_164626944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_332399104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 332399104 = ⟨686558300, 1517371741⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_166199552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_349176320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 349176320 = ⟨1325908926, 1750046054⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_174588160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_362808320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 362808320 = ⟨1931790297, 476503814⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_181404160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_365953536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 365953536 = ⟨1226786532, 672104075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_182976768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_382730752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 382730752 = ⟨395125700, 692627592⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_191365376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_396362752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 396362752 = ⟨1957773767, 58465136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_198181376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_399507968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 399507968 = ⟨224636281, 675815003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_199753984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_416285184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 416285184 = ⟨602467710, 2096252676⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_208142592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_429917184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 429917184 = ⟨290670999, 484618707⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_214958592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_433062400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 433062400 = ⟨494951206, 1645963625⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_216531200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_449839616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 449839616 = ⟨1907298563, 533181105⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_224919808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_463471616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 463471616 = ⟨1504211713, 91770747⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_231735808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_466616832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 466616832 = ⟨837172203, 2053414766⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_233308416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_483394048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 483394048 = ⟨922370475, 235968217⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_241697024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_497026048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 497026048 = ⟨1318032416, 914753745⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_248513024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_500171264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 500171264 = ⟨48116213, 88431926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_250085632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_516948480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 516948480 = ⟨1257023573, 1475625567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_258474240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_530580480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 530580480 = ⟨1184172815, 1501800213⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_265290240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_533725696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 533725696 = ⟨1400381890, 1991044605⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_266862848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_564134912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 564134912 = ⟨1298887220, 1511704801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_282067456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_597689344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 597689344 = ⟨602494260, 1130713038⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_298844672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_631243776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 631243776 = ⟨1399852939, 194390338⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_315621888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_664798208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 664798208 = ⟨781973549, 1825836746⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_332399104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_698352640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 698352640 = ⟨2109025845, 874384271⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_349176320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_731907072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 731907072 = ⟨1631477536, 1849469903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_365953536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_765461504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 765461504 = ⟨1316554005, 978872310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_382730752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_799015936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 799015936 = ⟨1494392856, 1308824302⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_399507968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_832570368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 832570368 = ⟨495658886, 727092399⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_416285184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_866124800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 866124800 = ⟨1384212302, 2102206331⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_433062400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_899679232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 899679232 = ⟨476503814, 215693350⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_449839616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_933233664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 933233664 = ⟨58465136, 189709880⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_466616832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_966788096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 966788096 = ⟨484618707, 1856812648⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_483394048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1000342528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1000342528 = ⟨91770747, 643271934⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_500171264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1033896960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1033896960 = ⟨914753745, 829451231⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_516948480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1067451392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1067451392 = ⟨1501800213, 963310832⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_533725696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 352) = ⟨635778846, 1298887220⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 352 = 27264000 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_27264000

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨635778846, 1298887220⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 352) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 353) = ⟨1298887220, 1511704801⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 353 = 564134912 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_564134912

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1298887220, 1511704801⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 353) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 354) = ⟨1420391248, 495658886⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 354 = 295699456 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_295699456

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1420391248, 495658886⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 354) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 355) = ⟨495658886, 727092399⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 355 = 832570368 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_832570368

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨495658886, 727092399⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 355) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 356) = ⟨1273099376, 2109025845⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 356 = 161481728 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_161481728

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1273099376, 2109025845⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 356) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 357) = ⟨2109025845, 874384271⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 357 = 698352640 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_698352640

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2109025845, 874384271⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 357) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 358) = ⟨290670999, 484618707⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 358 = 429917184 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_429917184

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨290670999, 484618707⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 358) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 359) = ⟨484618707, 1856812648⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 359 = 966788096 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_966788096

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨484618707, 1856812648⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 359) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 360) = ⟨1953093309, 1399852939⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 360 = 94372864 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_94372864

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1953093309, 1399852939⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 360) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 361) = ⟨1399852939, 194390338⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 361 = 631243776 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_631243776

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1399852939, 194390338⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 361) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 362) = ⟨1931790297, 476503814⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 362 = 362808320 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_362808320

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1931790297, 476503814⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 362) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 363) = ⟨476503814, 215693350⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 363 = 899679232 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_899679232

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨476503814, 215693350⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 363) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 364) = ⟨1168611337, 1316554005⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 364 = 228590592 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_228590592

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1168611337, 1316554005⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 364) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 365) = ⟨1316554005, 978872310⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 365 = 765461504 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_765461504

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1316554005, 978872310⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 365) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 366) = ⟨1318032416, 914753745⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 366 = 497026048 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_497026048

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1318032416, 914753745⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 366) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 367) = ⟨914753745, 829451231⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 367 = 1033896960 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1033896960

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨914753745, 829451231⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 367) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 368) = ⟨1016770609, 602494260⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 368 = 60818432 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_60818432

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1016770609, 602494260⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 368) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 369) = ⟨602494260, 1130713038⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 369 = 597689344 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_597689344

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨602494260, 1130713038⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 369) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 370) = ⟨45277316, 1384212302⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 370 = 329253888 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_329253888

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨45277316, 1384212302⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 370) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 371) = ⟨1384212302, 2102206331⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 371 = 866124800 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_866124800

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1384212302, 2102206331⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 371) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 372) = ⟨298013744, 1631477536⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 372 = 195036160 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_195036160

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨298013744, 1631477536⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 372) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 373) = ⟨1631477536, 1849469903⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 373 = 731907072 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_731907072

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1631477536, 1849469903⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 373) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 374) = ⟨1504211713, 91770747⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 374 = 463471616 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_463471616

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1504211713, 91770747⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 374) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 375) = ⟨91770747, 643271934⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 375 = 1000342528 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1000342528

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨91770747, 643271934⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 375) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 376) = ⟨321646901, 781973549⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 376 = 127927296 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_127927296

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨321646901, 781973549⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 376) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 377) = ⟨781973549, 1825836746⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 377 = 664798208 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_664798208

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨781973549, 1825836746⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 377) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 378) = ⟨1957773767, 58465136⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 378 = 396362752 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_396362752

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1957773767, 58465136⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 378) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 379) = ⟨58465136, 189709880⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 379 = 933233664 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_933233664

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨58465136, 189709880⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 379) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 380) = ⟨838659345, 1494392856⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 380 = 262145024 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_262145024

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨838659345, 1494392856⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 380) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 381) = ⟨1494392856, 1308824302⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 381 = 799015936 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_799015936

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1494392856, 1308824302⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 381) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 382) = ⟨1184172815, 1501800213⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 382 = 530580480 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_530580480

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1184172815, 1501800213⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 382) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 383) = ⟨1501800213, 963310832⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 383 = 1067451392 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1067451392

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1501800213, 963310832⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 383) := by
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

end R17TableAChunk11Certificate
