import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableBChunk05Certificate
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

theorem power_34 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34 = ⟨877671024, 692632976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17]
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

theorem power_40 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40 = ⟨1326739366, 1694702828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41 = ⟨2015439815, 1268983748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42 = ⟨292568953, 1233748517⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21]
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

theorem power_50 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50 = ⟨1661131656, 1602607662⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25]
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

theorem power_66 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66 = ⟨235324384, 1522698391⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69 = ⟨878709433, 901181160⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_70 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70 = ⟨115184242, 829081638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_74 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 74 = ⟨635582094, 405349503⟩ := by
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

theorem power_80 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 80 = ⟨251214192, 1557021428⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_82 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 82 = ⟨588340926, 1971636517⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_84 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84 = ⟨1543107831, 276086046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_85 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 85 = ⟨807730929, 1079284455⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_86 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86 = ⟨1687815885, 1893568127⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90 = ⟨430426420, 308360131⟩ := by
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

theorem power_98 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98 = ⟨1757883680, 2146872443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_101 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101 = ⟨1779769850, 1133066291⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102 = ⟨1516486685, 2082671253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104 = ⟨595835346, 937999867⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106 = ⟨382757218, 311908650⟩ := by
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

theorem power_114 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114 = ⟨1901921750, 225130802⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_116 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116 = ⟨894357328, 342875169⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_117 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117 = ⟨1804617719, 1766370095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_118 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118 = ⟨2029146254, 280154270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122 = ⟨910427772, 437706403⟩ := by
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

theorem power_133 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 133 = ⟨697736105, 1609499589⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_138 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 138 = ⟨289576174, 117745875⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_141 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 141 = ⟨1089936147, 199619290⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_148 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 148 = ⟨1797069868, 1569931230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_149 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 149 = ⟨1021562393, 1112546712⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74]
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

theorem power_160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 160 = ⟨352777635, 313115116⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_165 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 165 = ⟨1912338015, 1472102703⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 168 = ⟨502934906, 432562679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_170 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 170 = ⟨1200476557, 337352944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_173 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 173 = ⟨172481178, 435324837⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_180 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 180 = ⟨440283696, 1083008219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_181 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 181 = ⟨1696217250, 537553639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90]
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

theorem power_197 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 197 = ⟨929859587, 264346242⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_202 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 202 = ⟨1860360142, 751729554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_205 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 205 = ⟨1921054693, 699847975⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 208 = ⟨1397719779, 1280626794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_212 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 212 = ⟨224723496, 98912589⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_213 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 213 = ⟨1005480520, 1074898100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106]
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

theorem power_229 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 229 = ⟨1000103727, 1053059015⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 232 = ⟨1705761383, 185122675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_234 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 234 = ⟨1023252104, 151076554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_237 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 237 = ⟨1434289749, 1293959886⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_244 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 244 = ⟨840379230, 2035177650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_245 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 245 = ⟨58842794, 1641594984⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122]
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

theorem power_266 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 266 = ⟨1886029052, 1532389385⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_276 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 276 = ⟨2136981225, 76442191⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_138]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_282 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 282 = ⟨1157625612, 1914432435⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_141]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 296 = ⟨224965265, 159335170⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_148]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_298 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 298 = ⟨1987234348, 1575849251⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_149]
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

theorem power_320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 320 = ⟨1637047685, 109864373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_330 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 330 = ⟨499846262, 739901923⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_165]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 336 = ⟨180537201, 1575865056⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_340 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 340 = ⟨1035137668, 1694074029⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_170]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_346 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 346 = ⟨164892227, 1820409188⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_173]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 360 = ⟨1022383927, 1626835633⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_180]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_362 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 362 = ⟨1653955205, 1266544038⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_181]
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

theorem power_394 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 394 = ⟨1502978530, 1510529028⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_197]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_404 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 404 = ⟨1264991587, 1665650581⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_202]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_410 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 410 = ⟨1593040053, 504124593⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_205]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 416 = ⟨1719486678, 1121851154⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 424 = ⟨167179466, 382336254⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_212]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_426 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 426 = ⟨740193435, 419472664⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_213]
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

theorem power_458 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 458 = ⟨1423811280, 1075984596⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_229]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 464 = ⟨761225645, 1514363314⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_468 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 468 = ⟨2093397897, 1522550679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_234]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_474 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 474 = ⟨1093702517, 1838031466⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_237]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 488 = ⟨1001236781, 1044516446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_244]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_490 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 490 = ⟨1244644911, 1069588596⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_245]
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

theorem power_532 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 532 = ⟨285160156, 357127343⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_266]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 552 = ⟨1478094092, 46019520⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_276]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_564 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 564 = ⟨990133713, 890342639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_282]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 592 = ⟨462102546, 1660293932⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_596 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 596 = ⟨1491797637, 1365652507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_298]
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

theorem power_640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 640 = ⟨982766847, 1369509443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_660 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 660 = ⟨224203845, 414234931⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_330]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 672 = ⟨1863904991, 681598711⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 680 = ⟨1444330179, 873729398⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_340]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_692 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 692 = ⟨755576242, 883344195⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_346]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 720 = ⟨330499511, 1255545984⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_724 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 724 = ⟨1031951347, 729196118⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_362]
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

theorem power_788 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 788 = ⟨1950981915, 1375812553⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_394]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 808 = ⟨1343024069, 808079406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_404]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_820 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 820 = ⟨1621830008, 530224415⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_410]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 832 = ⟨529167155, 49384636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 848 = ⟨639667341, 414959610⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_852 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 852 = ⟨1095473796, 1598161515⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_426]
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

theorem power_916 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 916 = ⟨1977654507, 446409834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_458]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 928 = ⟨192925011, 1863974752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 936 = ⟨977714903, 1051251569⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_468]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_948 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 948 = ⟨1476786005, 180925149⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_474]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 976 = ⟨1625484020, 323681644⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_980 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 980 = ⟨1801197367, 627878655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_490]
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

theorem power_1064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1064 = ⟨1028189478, 1432821515⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_532]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1104 = ⟨1224066945, 216858013⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1128 = ⟨1565940610, 1178187397⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_564]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1184 = ⟨1392219141, 868524623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1192 = ⟨1278915379, 156031814⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_596]
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

theorem power_1280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1280 = ⟨1774187400, 1713497086⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1320 = ⟨2118388939, 778673083⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_660]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1344 = ⟨1447121614, 1053732556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1360 = ⟨1062534928, 1483827896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1384 = ⟨1158220058, 1179641218⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_692]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1440 = ⟨1445302729, 1296213244⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1448 = ⟨331639486, 137962451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_724]
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

theorem power_1576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1576 = ⟨64769829, 707320841⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_788]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1616 = ⟨190241594, 1357019236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1640 = ⟨1813157545, 1272324159⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_820]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1664 = ⟨288424812, 1959942454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1696 = ⟨797688518, 1724894293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1704 = ⟨533992267, 1222429731⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_852]
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

theorem power_1832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1832 = ⟨1811599737, 1651618790⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_916]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1856 = ⟨2162587, 1662102570⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1872 = ⟨1690319162, 1749624555⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1896 = ⟨161393962, 1843672076⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_948]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1952 = ⟨1871828618, 1847683492⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1960 = ⟨190729669, 1803211581⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_980]
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

theorem power_2128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2128 = ⟨1959664240, 1343172434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2208 = ⟨1676955329, 1180692240⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2256 = ⟨674941568, 69635140⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2368 = ⟨39852141, 123936243⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2384 = ⟨1273255873, 638520824⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1192]
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

theorem power_2560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2560 = ⟨1743980363, 345791924⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2640 = ⟨974359725, 754960039⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2688 = ⟨319360190, 618255967⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2720 = ⟨1072531720, 1896677731⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2768 = ⟨449129006, 1767494420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2880 = ⟨2050207099, 979596272⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2896 = ⟨754893878, 907943051⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1448]
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

theorem power_3152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3152 = ⟨2086360188, 1335899009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3232 = ⟨124445571, 706631523⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3280 = ⟨2002499842, 1064027224⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3328 = ⟨1399167609, 1906303117⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3392 = ⟨968612238, 1641022910⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3408 = ⟨1328324961, 803287742⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1704]
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

theorem power_3664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3664 = ⟨430184902, 2122941069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3712 = ⟨1273782452, 924138332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3744 = ⟨103855733, 1898302976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3792 = ⟨1399177187, 613275639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3904 = ⟨314388810, 1013513450⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3920 = ⟨1184704737, 1073695025⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1960]
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

theorem power_4256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4256 = ⟨1931712912, 754673528⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4416 = ⟨408933184, 381501510⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4512 = ⟨1571173152, 1297316795⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4736 = ⟨272617121, 579551580⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4768 = ⟨1639439199, 2098400799⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2384]
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

theorem power_5120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5120 = ⟨235158087, 2112924242⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5280 = ⟨1521143491, 1687728277⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5376 = ⟨967187167, 1461124768⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5440 = ⟨607008739, 948334533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5536 = ⟨514904628, 1852012252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5760 = ⟨175645010, 1734378279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5792 = ⟨582466233, 38339503⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2896]
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

theorem power_6304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6304 = ⟨162898390, 1970049448⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6464 = ⟨976698970, 920955611⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6560 = ⟨819553148, 474842885⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6656 = ⟨1510720600, 1956487951⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6784 = ⟨1220597866, 72538165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6816 = ⟨1545116424, 2064043564⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3408]
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

theorem power_7328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7328 = ⟨1926652717, 428844655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7424 = ⟨719349967, 2102971509⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7488 = ⟨1416522298, 2020079164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7584 = ⟨1116836362, 1045930896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7808 = ⟨1996451271, 146269947⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7840 = ⟨988509914, 508843856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3920]
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

theorem power_8512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8512 = ⟨1109321131, 138320471⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8832 = ⟨2028834280, 858819348⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9024 = ⟨947141678, 1574276826⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9472 = ⟨2016094574, 1147504298⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9536 = ⟨1288616871, 1536669085⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4768]
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

theorem power_10240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10240 = ⟨1242192167, 1322293366⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10560 = ⟨1013382771, 1429471715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10752 = ⟨133802874, 733650364⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10880 = ⟨134399697, 892423737⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11072 = ⟨1458201270, 987288878⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11520 = ⟨1411573869, 756888130⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11584 = ⟨1412692279, 676395092⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5792]
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

theorem power_12608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12608 = ⟨391042756, 974739797⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12928 = ⟨2024521721, 865260240⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13120 = ⟨1124810688, 1033695992⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13312 = ⟨721344225, 1097609337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13568 = ⟨1050297291, 98481735⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13632 = ⟨1665935276, 1734295473⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6816]
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

theorem power_14656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14656 = ⟨1633565514, 1655430508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14848 = ⟨520833839, 1618182004⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14976 = ⟨2067447709, 1097691368⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15168 = ⟨444881175, 526464189⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15616 = ⟨139198880, 1155184073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15680 = ⟨487689472, 284064100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7840]
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

theorem power_17024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17024 = ⟨1619953932, 346710098⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17664 = ⟨15796839, 1693524553⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18048 = ⟨561474802, 2081083045⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18944 = ⟨83021569, 1776986900⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19072 = ⟨1087399768, 299521376⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9536]
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

theorem power_20480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20480 = ⟨433600440, 167145119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21120 = ⟨169513512, 2043020633⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21504 = ⟨1700714437, 566394792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21760 = ⟨207134484, 1863212449⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22144 = ⟨999880307, 529086317⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23040 = ⟨512700922, 986405252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23168 = ⟨466922503, 476127114⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11584]
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

theorem power_25216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25216 = ⟨531994522, 589272094⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25856 = ⟨1354554672, 1833839332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26240 = ⟨1526443891, 484288181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26624 = ⟨2056541252, 1900478857⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27136 = ⟨698096929, 432547149⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27264 = ⟨1385933946, 1155521422⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13632]
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

theorem power_29312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29312 = ⟨1816695102, 1289326046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29696 = ⟨1800149012, 1373092732⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29952 = ⟨1852134147, 634458272⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30336 = ⟨1617861171, 235619726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31232 = ⟨1863885482, 1326705008⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31360 = ⟨478538903, 11590567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15680]
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

theorem power_34048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34048 = ⟨923306421, 1161192049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35328 = ⟨750253747, 530937643⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36096 = ⟨1211248826, 185397697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37888 = ⟨451882769, 1853894340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38144 = ⟨1930645967, 1155688905⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19072]
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

theorem power_40960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40960 = ⟨263253631, 1948074535⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42240 = ⟨1220257075, 155758384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43008 = ⟨1503715524, 748528002⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43520 = ⟨1133865341, 1051269249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44288 = ⟨1730274123, 949691994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46080 = ⟨2092093316, 989477899⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46336 = ⟨1048380476, 1956147418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23168]
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

theorem power_50432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50432 = ⟨449576803, 1250724952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51712 = ⟨554838094, 2082603647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52480 = ⟨1087936139, 1292268408⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53248 = ⟨528497962, 2048433423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54272 = ⟨1176403617, 782773078⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54528 = ⟨1518385385, 591293547⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27264]
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

theorem power_58624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58624 = ⟨1640223361, 1258059286⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59392 = ⟨1076514332, 1068664781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59904 = ⟨486461911, 1395218254⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60672 = ⟨1387747854, 56474655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62464 = ⟨1733341057, 673759763⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62720 = ⟨2077215075, 695458097⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31360]
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

theorem power_68096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 68096 = ⟨102310340, 81272348⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_70656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70656 = ⟨1921779281, 131885⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72192 = ⟨894280518, 1968367347⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_75776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 75776 = ⟨1210077794, 246102266⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76288 = ⟨1084669591, 1925834344⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38144]
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

theorem power_84480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84480 = ⟨954329647, 1601612428⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_86016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86016 = ⟨36975016, 821963373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87040 = ⟨290570175, 898698902⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88576 = ⟨544822653, 2069348221⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92160 = ⟨713314261, 425545952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92672 = ⟨576129160, 699868407⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46336]
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

theorem power_100864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100864 = ⟨1321798221, 991073372⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_103424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103424 = ⟨733457982, 495056491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104960 = ⟨132278529, 1557996220⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106496 = ⟨1488671228, 939868393⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108544 = ⟨1032881673, 494228663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_109056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109056 = ⟨85627671, 1011996137⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54528]
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

theorem power_117248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117248 = ⟨1418966850, 1211837697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_118784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118784 = ⟨845078094, 149898124⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_119808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119808 = ⟨1114403665, 611529715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121344 = ⟨441161107, 456269102⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124928 = ⟨346773666, 152947344⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125440 = ⟨1284671812, 504899699⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62720]
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

theorem power_136192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 136192 = ⟨437058642, 1419738284⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_141312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 141312 = ⟨1719915550, 648525961⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_144384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 144384 = ⟨1692492513, 693418291⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_151552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 151552 = ⟨2001642678, 1520422911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_152576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 152576 = ⟨885008830, 1594173084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76288]
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

theorem power_168960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 168960 = ⟨1279156361, 1548443426⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_172032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 172032 = ⟨735504938, 198004457⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_174080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 174080 = ⟨229177162, 396528583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_177152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 177152 = ⟨1776728469, 999929976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_184320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 184320 = ⟨1029245122, 1158447597⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_185344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 185344 = ⟨1809743850, 388676761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92672]
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

theorem power_201728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 201728 = ⟨329561842, 1307878404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_206848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 206848 = ⟨1817546580, 1225707862⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_209920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 209920 = ⟨1050954735, 1201222275⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_217088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 217088 = ⟨1876139646, 119923533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_218112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 218112 = ⟨919013925, 1686206068⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109056]
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

theorem power_234496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 234496 = ⟨29093893, 259327061⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_237568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 237568 = ⟨474711937, 1020011657⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_239616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 239616 = ⟨1300505822, 1483719533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_242688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 242688 = ⟨970631068, 228952312⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_249856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 249856 = ⟨887385898, 608769478⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_250880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 250880 = ⟨1374751140, 1733176008⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125440]
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

theorem power_272384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 272384 = ⟨459121708, 1982887005⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_136192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_282624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 282624 = ⟨18918067, 521344418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_141312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_288768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 288768 = ⟨443122237, 696551100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_144384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_303104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 303104 = ⟨1479292912, 403634516⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_151552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_305152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 305152 = ⟨1394038486, 1247069276⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_152576]
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

theorem power_337920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 337920 = ⟨1482323122, 40945560⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_168960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_348160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 348160 = ⟨183117139, 65944434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_174080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_354304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 354304 = ⟨533049899, 1473067927⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_177152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_368640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 368640 = ⟨1362074261, 2047718881⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_184320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_370688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 370688 = ⟨559088903, 1739101071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_185344]
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

theorem power_403456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 403456 = ⟨799108626, 281610748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_201728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_413696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 413696 = ⟨1936661821, 241049853⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_206848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_419840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 419840 = ⟨114019110, 1704020237⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_209920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_434176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 434176 = ⟨386684296, 1363813538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_217088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_436224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 436224 = ⟨1924931282, 420158453⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_218112]
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

theorem power_468992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 468992 = ⟨616220563, 21676868⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_234496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_479232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 479232 = ⟨174156438, 1448257952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_239616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_485376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 485376 = ⟨1797665716, 1562938324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_242688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_499712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 499712 = ⟨836848068, 529120781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_249856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_501760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 501760 = ⟨1194561107, 2080170062⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_250880]
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

theorem power_544768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 544768 = ⟨2117360294, 299533990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_272384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_565248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 565248 = ⟨153716819, 2054656334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_282624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_577536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 577536 = ⟨58617043, 693726782⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_288768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_610304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 610304 = ⟨1672578949, 179250121⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_305152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_630784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 630784 = ⟨1542296538, 1163978019⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_315392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_643072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 643072 = ⟨25637092, 421692094⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_321536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_675840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 675840 = ⟨1051514954, 1945490652⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_337920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_696320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 696320 = ⟨2083960347, 2126322313⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_348160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_708608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 708608 = ⟨1210158521, 1506582976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_354304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_741376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 741376 = ⟨849384769, 61803180⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_370688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_761856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 761856 = ⟨1739468984, 977169647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_380928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_774144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 774144 = ⟨852276839, 226974950⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_387072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_806912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 806912 = ⟨526492512, 1146089824⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_403456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_827392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 827392 = ⟨682480399, 799350698⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_413696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_839680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 839680 = ⟨799756877, 308500462⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_419840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_872448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 872448 = ⟨1845239625, 562344050⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_436224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_892928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 892928 = ⟨1834599352, 1895440138⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_446464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_905216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 905216 = ⟨69829270, 1352453515⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_452608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_937984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 937984 = ⟨2138570352, 385731389⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_468992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_958464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 958464 = ⟨1439180125, 915904269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_479232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_970752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 970752 = ⟨1797669071, 2141355836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_485376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1003520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1003520 = ⟨1805314849, 466904232⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_501760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1024000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1024000 = ⟨581559614, 117257650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_512000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1036288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1036288 = ⟨2126452532, 708823575⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_518144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1089536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1089536 = ⟨804296458, 213396278⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_544768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1155072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1155072 = ⟨1982402, 431614399⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_577536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1220608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1220608 = ⟨848969192, 1414511411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_610304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1286144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1286144 = ⟨1134947640, 394118266⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_643072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1351680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1351680 = ⟨565878948, 1786880501⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_675840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1417216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1417216 = ⟨563752921, 1285853654⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_708608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1482752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1482752 = ⟨1083568418, 725197280⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_741376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1548288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1548288 = ⟨210740911, 1280364462⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_774144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1613824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1613824 = ⟨2104095544, 1435777142⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_806912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1679360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1679360 = ⟨1244152270, 498961107⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_839680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1744896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1744896 = ⟨1209545065, 1852982367⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_872448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1810432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1810432 = ⟨227977990, 1816535211⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_905216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1875968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1875968 = ⟨1340472519, 1675598842⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_937984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1941504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1941504 = ⟨1662799443, 1810348412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_970752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2007040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2007040 = ⟨1480502711, 1450760425⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1003520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2072576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2072576 = ⟨510094092, 641201894⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1036288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 160) = ⟨263253631, 1948074535⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 160 = 40960 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_40960

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨263253631, 1948074535⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 160) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 161) = ⟨804296458, 213396278⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 161 = 1089536 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1089536

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨804296458, 213396278⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 161) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 162) = ⟨153716819, 2054656334⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 162 = 565248 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_565248

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨153716819, 2054656334⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 162) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 163) = ⟨2104095544, 1435777142⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 163 = 1613824 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1613824

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2104095544, 1435777142⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 163) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 164) = ⟨1479292912, 403634516⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 164 = 303104 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_303104

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1479292912, 403634516⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 164) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 165) = ⟨565878948, 1786880501⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 165 = 1351680 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1351680

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨565878948, 1786880501⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 165) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 166) = ⟨682480399, 799350698⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 166 = 827392 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_827392

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨682480399, 799350698⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 166) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 167) = ⟨1340472519, 1675598842⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 167 = 1875968 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1875968

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1340472519, 1675598842⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 167) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 168) = ⟨735504938, 198004457⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 168 = 172032 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_172032

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨735504938, 198004457⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 168) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 169) = ⟨848969192, 1414511411⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 169 = 1220608 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1220608

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨848969192, 1414511411⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 169) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 170) = ⟨2083960347, 2126322313⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 170 = 696320 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_696320

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2083960347, 2126322313⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 170) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 171) = ⟨1209545065, 1852982367⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 171 = 1744896 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1744896

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1209545065, 1852982367⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 171) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 172) = ⟨386684296, 1363813538⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 172 = 434176 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_434176

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨386684296, 1363813538⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 172) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 173) = ⟨1083568418, 725197280⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 173 = 1482752 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1482752

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1083568418, 725197280⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 173) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 174) = ⟨1439180125, 915904269⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 174 = 958464 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_958464

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1439180125, 915904269⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 174) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 175) = ⟨1480502711, 1450760425⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 175 = 2007040 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2007040

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1480502711, 1450760425⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 175) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 176) = ⟨1488671228, 939868393⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 176 = 106496 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_106496

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1488671228, 939868393⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 176) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 177) = ⟨1982402, 431614399⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 177 = 1155072 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1155072

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1982402, 431614399⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 177) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 178) = ⟨1542296538, 1163978019⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 178 = 630784 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_630784

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1542296538, 1163978019⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 178) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 179) = ⟨1244152270, 498961107⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 179 = 1679360 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1679360

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1244152270, 498961107⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 179) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 180) = ⟨1362074261, 2047718881⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 180 = 368640 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_368640

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1362074261, 2047718881⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 180) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 181) = ⟨563752921, 1285853654⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 181 = 1417216 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1417216

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨563752921, 1285853654⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 181) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 182) = ⟨1834599352, 1895440138⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 182 = 892928 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_892928

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1834599352, 1895440138⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 182) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 183) = ⟨1662799443, 1810348412⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 183 = 1941504 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1941504

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1662799443, 1810348412⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 183) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 184) = ⟨474711937, 1020011657⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 184 = 237568 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_237568

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨474711937, 1020011657⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 184) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 185) = ⟨1134947640, 394118266⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 185 = 1286144 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1286144

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1134947640, 394118266⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 185) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 186) = ⟨1739468984, 977169647⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 186 = 761856 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_761856

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1739468984, 977169647⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 186) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 187) = ⟨227977990, 1816535211⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 187 = 1810432 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1810432

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨227977990, 1816535211⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 187) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 188) = ⟨836848068, 529120781⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 188 = 499712 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_499712

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨836848068, 529120781⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 188) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 189) = ⟨210740911, 1280364462⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 189 = 1548288 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1548288

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨210740911, 1280364462⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 189) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 190) = ⟨581559614, 117257650⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 190 = 1024000 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1024000

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨581559614, 117257650⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 190) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 191) = ⟨510094092, 641201894⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 191 = 2072576 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2072576

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨510094092, 641201894⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 191) := by
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

end R17TableBChunk05Certificate
