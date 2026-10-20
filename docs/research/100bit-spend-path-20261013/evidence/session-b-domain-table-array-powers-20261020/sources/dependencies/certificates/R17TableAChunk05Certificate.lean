import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk05Certificate
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

theorem power_20481 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20481 = ⟨1791402756, 441607032⟩ := by
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

theorem power_40962 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40962 = ⟨1981846687, 650646126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20481]
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

theorem power_53249 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53249 = ⟨1607196605, 225621868⟩ := by
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

theorem power_81924 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81924 = ⟨2115545634, 1290450103⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40962]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_84480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84480 = ⟨954329647, 1601612428⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_86017 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86017 = ⟨185307065, 605556115⟩ := by
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

theorem power_106498 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106498 = ⟨1307929789, 1482300573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53249]
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

theorem power_118785 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118785 = ⟨397632992, 271750681⟩ := by
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

theorem power_151553 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 151553 = ⟨1357366543, 1841378403⟩ := by
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

theorem power_163848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 163848 = ⟨391348336, 1144440033⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81924]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_168960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 168960 = ⟨1279156361, 1548443426⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_172034 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 172034 = ⟨588538591, 1556774907⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86017]
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

theorem power_184321 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 184321 = ⟨175966347, 900319083⟩ := by
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

theorem power_212996 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 212996 = ⟨1658470877, 525594962⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106498]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_217089 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 217089 = ⟨1262751543, 2137542133⟩ := by
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

theorem power_237570 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 237570 = ⟨1213984790, 770439925⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118785]
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

theorem power_249857 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 249857 = ⟨1617546786, 1074812389⟩ := by
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

theorem power_282625 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 282625 = ⟨331064760, 732167591⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_141312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_288768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 288768 = ⟨443122237, 696551100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_144384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_303106 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 303106 = ⟨399172028, 749566560⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_151553]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_305152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 305152 = ⟨1394038486, 1247069276⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_152576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_315393 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 315393 = ⟨829145081, 1923350948⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_157696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_321536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 321536 = ⟨1102231607, 609468827⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_160768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_327696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 327696 = ⟨1520489281, 630190989⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_163848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_337920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 337920 = ⟨1482323122, 40945560⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_168960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_344068 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 344068 = ⟨961105699, 115044329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_172034]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_348161 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 348161 = ⟨1503086048, 1583419858⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_174080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_354304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 354304 = ⟨533049899, 1473067927⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_177152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_368642 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 368642 = ⟨1774583265, 102669342⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_184321]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_370688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 370688 = ⟨559088903, 1739101071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_185344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_380929 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 380929 = ⟨496706151, 1179855108⟩ := by
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

theorem power_413697 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 413697 = ⟨86267784, 1594508749⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_206848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_419840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 419840 = ⟨114019110, 1704020237⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_209920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_425992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 425992 = ⟨2069578647, 797289285⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_212996]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_434178 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 434178 = ⟨2026031018, 99741119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_217089]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_436224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 436224 = ⟨1924931282, 420158453⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_218112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_446465 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 446465 = ⟨1771020212, 606422531⟩ := by
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

theorem power_475140 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 475140 = ⟨862577675, 1228141629⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_237570]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_479233 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 479233 = ⟨1260280250, 1089446561⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_239616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_485376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 485376 = ⟨1797665716, 1562938324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_242688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_499714 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 499714 = ⟨217813593, 1693435599⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_249857]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_501760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 501760 = ⟨1194561107, 2080170062⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_250880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_512001 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 512001 = ⟨1194632758, 298949850⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_256000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_518144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 518144 = ⟨1187658047, 1597100399⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_259072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_544769 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 544769 = ⟨1461677992, 489844593⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_272384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_565250 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 565250 = ⟨843249938, 170166663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_282625]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_577537 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 577537 = ⟨1922117988, 826105968⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_288768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_606212 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 606212 = ⟨542136706, 292378⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_303106]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_610305 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 610305 = ⟨1864257977, 2091373427⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_305152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_630786 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 630786 = ⟨1583395774, 1025277020⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_315393]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_643073 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 643073 = ⟨1722117645, 1604839244⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_321536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_655392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 655392 = ⟨1736332107, 671411702⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_327696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_675841 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 675841 = ⟨931913181, 1368474784⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_337920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_688136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 688136 = ⟨1411393152, 1779937831⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_344068]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_696322 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 696322 = ⟨993253, 190084186⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_348161]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_708609 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 708609 = ⟨1127887733, 524321327⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_354304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_737284 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 737284 = ⟨1123093775, 782950236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_368642]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_741377 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 741377 = ⟨1712036836, 1438011726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_370688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_761858 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 761858 = ⟨342170137, 1630549762⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_380929]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_774145 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 774145 = ⟨1739312855, 206728268⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_387072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_806913 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 806913 = ⟨1962792413, 428643429⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_403456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_827394 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 827394 = ⟨415576783, 564544775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_413697]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_839681 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 839681 = ⟨790876562, 814965322⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_419840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_851984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 851984 = ⟨1613239315, 1945948878⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_425992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_868356 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 868356 = ⟨379598675, 1973578070⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_434178]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_872449 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 872449 = ⟨867454222, 1822226334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_436224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_892930 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 892930 = ⟨462336886, 173699728⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_446465]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_905217 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 905217 = ⟨670035334, 1297898456⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_452608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_937985 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 937985 = ⟨295406645, 814064053⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_468992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_950280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 950280 = ⟨631284630, 945564145⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_475140]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_958466 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 958466 = ⟨507569912, 994042343⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_479233]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_970753 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 970753 = ⟨1244238904, 1849595217⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_485376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_999428 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 999428 = ⟨1325496739, 65015908⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_499714]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1003521 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1003521 = ⟨1694904518, 217259571⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_501760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1024002 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1024002 = ⟨451748575, 339482256⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_512001]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1036289 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1036289 = ⟨1644448144, 2130807204⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_518144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1089538 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1089538 = ⟨1298121601, 32713004⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_544769]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1130500 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1130500 = ⟨1991308744, 775888276⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_565250]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1155074 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1155074 = ⟨1723164536, 1306738774⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_577537]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1212424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1212424 = ⟨828901993, 1860716302⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_606212]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1220610 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1220610 = ⟨533883193, 2143322826⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_610305]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1261572 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1261572 = ⟨882058275, 995061139⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_630786]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1286146 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1286146 = ⟨1958958007, 1396025270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_643073]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1310784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1310784 = ⟨221709668, 403693286⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_655392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1351682 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1351682 = ⟨2025863311, 836228478⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_675841]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1376272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1376272 = ⟨975762742, 1305092223⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_688136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1392644 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1392644 = ⟨1713056071, 588923871⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_696322]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1417218 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1417218 = ⟨2035660699, 2096475349⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_708609]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1474568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1474568 = ⟨1809171606, 2126348309⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_737284]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1482754 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1482754 = ⟨197183778, 546530466⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_741377]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1523716 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1523716 = ⟨189136103, 488881997⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_761858]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1548290 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1548290 = ⟨547373086, 1111093758⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_774145]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1613826 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1613826 = ⟨953358229, 301886068⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_806913]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1654788 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1654788 = ⟨585976953, 2007393719⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_827394]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1679362 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1679362 = ⟨1303387745, 1050434624⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_839681]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1703968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1703968 = ⟨528369700, 1192974639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_851984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1736712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1736712 = ⟨2003386606, 766087601⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_868356]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1744898 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1744898 = ⟨931672135, 1343173335⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_872449]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1785860 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1785860 = ⟨2102008416, 63716043⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_892930]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1810434 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1810434 = ⟨2048307511, 2085904922⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_905217]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1875970 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1875970 = ⟨1120412281, 683301334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_937985]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1900560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1900560 = ⟨372246560, 567069475⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_950280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1916932 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1916932 = ⟨1729247960, 1228065577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_958466]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1941506 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1941506 = ⟨896653892, 1069086591⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_970753]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1998856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1998856 = ⟨1873453028, 476320369⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_999428]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2007042 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2007042 = ⟨1016937682, 1882899253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1003521]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2048004 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2048004 = ⟨1319114620, 1171321236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1024002]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2072578 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2072578 = ⟨1499726738, 1641889112⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1036289]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2179076 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2179076 = ⟨1872923578, 1892417222⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1089538]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2261000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2261000 = ⟨1510951965, 41925877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1130500]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2310148 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2310148 = ⟨1473760380, 1634498503⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1155074]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2424848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2424848 = ⟨1973204787, 219513697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1212424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2441220 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2441220 = ⟨1163536147, 233911045⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1220610]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2523144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2523144 = ⟨633874068, 1309946662⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1261572]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2572292 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2572292 = ⟨1297792316, 1216937601⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1286146]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2621568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2621568 = ⟨1961142172, 317130913⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1310784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2703364 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2703364 = ⟨1238422830, 1469187741⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1351682]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2752544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2752544 = ⟨1012606319, 769245543⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1376272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2785288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2785288 = ⟨1110065787, 525981078⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1392644]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2834436 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2834436 = ⟨1396867266, 452044665⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1417218]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2949136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2949136 = ⟨1859494688, 951084732⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1474568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2965508 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2965508 = ⟨2083871459, 2659554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1482754]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3047432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3047432 = ⟨1387760729, 969332615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1523716]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3096580 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3096580 = ⟨2076170341, 500597693⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1548290]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3227652 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3227652 = ⟨1443388149, 1954199957⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1613826]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3309576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3309576 = ⟨953398140, 433248304⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1654788]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3358724 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3358724 = ⟨608399170, 1008554803⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1679362]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3407936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3407936 = ⟨789043502, 823988841⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1703968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3473424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3473424 = ⟨238276887, 377997448⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1736712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3489796 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3489796 = ⟨1564777512, 1197883299⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1744898]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3571720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3571720 = ⟨2041910484, 401120457⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1785860]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3620868 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3620868 = ⟨556318544, 764349301⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1810434]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3751940 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3751940 = ⟨1360524114, 1625640249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1875970]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3801120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3801120 = ⟨540357025, 2092743798⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1900560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3833864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3833864 = ⟨1842077464, 258736573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1916932]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3883012 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3883012 = ⟨1356931113, 689721428⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1941506]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3997712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3997712 = ⟨808429474, 247887875⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1998856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4014084 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4014084 = ⟨1769376991, 1563815108⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2007042]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4096008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4096008 = ⟨988205523, 748153287⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2048004]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4145156 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4145156 = ⟨420758721, 1966776532⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2072578]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4358152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4358152 = ⟨571504586, 1517388856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2179076]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4522000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4522000 = ⟨1254719563, 1432125987⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2261000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4620296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4620296 = ⟨1070416821, 938681156⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2310148]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4849696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4849696 = ⟨648439268, 1487561911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2424848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4882440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4882440 = ⟨1171028496, 804833138⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2441220]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5046288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5046288 = ⟨1080977835, 1543653298⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2523144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5144584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5144584 = ⟨1101145118, 744583114⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2572292]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5243136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5243136 = ⟨213507746, 1612896875⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2621568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5406728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5406728 = ⟨95303749, 630976574⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2703364]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5505088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5505088 = ⟨229766208, 657780499⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2752544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5570576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5570576 = ⟨1604752182, 1437164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2785288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5668872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5668872 = ⟨1306913049, 1898723326⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2834436]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5898272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5898272 = ⟨1985262049, 905020199⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2949136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5931016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5931016 = ⟨1167308605, 1720300310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2965508]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6094864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6094864 = ⟨1531401197, 296483655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3047432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6193160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6193160 = ⟨1183372937, 1967823205⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3096580]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6455304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6455304 = ⟨1256772219, 256383349⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3227652]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6619152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6619152 = ⟨1794276989, 1419933494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3309576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6717448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6717448 = ⟨240696895, 1946613324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3358724]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6815872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6815872 = ⟨471175289, 595459865⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3407936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6946848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6946848 = ⟨2131228046, 218368541⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3473424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6979592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6979592 = ⟨1357724641, 304589379⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3489796]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7143440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7143440 = ⟨577132092, 1433699063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3571720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7241736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7241736 = ⟨18813243, 1118470815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3620868]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7503880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7503880 = ⟨1858221413, 1350838027⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3751940]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7602240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7602240 = ⟨1019702360, 1831617453⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3801120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7667728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7667728 = ⟨1095933400, 1568320701⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3833864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7766024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7766024 = ⟨1047426414, 650296196⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3883012]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7995424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7995424 = ⟨449389558, 1610459201⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3997712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8028168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8028168 = ⟨1610296918, 87162498⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4014084]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8192016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8192016 = ⟨1416758422, 1958792201⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4096008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8290312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8290312 = ⟨252841763, 518465213⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4145156]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8716304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8716304 = ⟨1153194570, 1530154055⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4358152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9044000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9044000 = ⟨2072420105, 17627297⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4522000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9240592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9240592 = ⟨1865362323, 217333469⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4620296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9699392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9699392 = ⟨265465791, 165379811⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4849696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9764880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9764880 = ⟨327546493, 590549441⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4882440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10092576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10092576 = ⟨906035779, 1131728723⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5046288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10289168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10289168 = ⟨829414187, 192047248⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5144584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10486272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10486272 = ⟨1913293905, 1756479371⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5243136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10813456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10813456 = ⟨2027264061, 46739767⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5406728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11010176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11010176 = ⟨1442994695, 282953238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5505088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11141152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11141152 = ⟨877811037, 1856908749⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5570576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11337744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11337744 = ⟨683768753, 448466276⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5668872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11796544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11796544 = ⟨558534533, 859383112⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5898272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11862032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11862032 = ⟨1980784924, 845540203⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5931016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12189728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12189728 = ⟨1344420090, 838174390⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6094864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12386320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12386320 = ⟨1886332031, 2061592979⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6193160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12910608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12910608 = ⟨1739178982, 1392467835⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6455304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13238304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13238304 = ⟨6122462, 998725062⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6619152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13434896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13434896 = ⟨2090497353, 793276866⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6717448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13631744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13631744 = ⟨118986767, 767842995⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6815872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13893696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13893696 = ⟨1992150289, 423779487⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6946848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13959184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13959184 = ⟨2139847827, 1765215352⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6979592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14286880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14286880 = ⟨473308002, 2103304752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7143440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14483472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14483472 = ⟨1189793487, 1100896734⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7241736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15007760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15007760 = ⟨1209784465, 1819595660⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7503880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15204480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15204480 = ⟨1997346058, 506211542⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7602240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15335456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15335456 = ⟨571574212, 962630682⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7667728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15532048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15532048 = ⟨229783729, 167729385⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7766024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15990848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15990848 = ⟨1978156580, 1774181850⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7995424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16056336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16056336 = ⟨33527079, 197415158⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8028168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16384032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16384032 = ⟨2059806449, 308309538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8192016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16580624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16580624 = ⟨2066659777, 697934612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8290312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17432608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17432608 = ⟨1659020535, 572129379⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8716304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18088000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18088000 = ⟨2061167384, 810851564⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9044000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18481184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18481184 = ⟨1139879612, 1061525765⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9240592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19398784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19398784 = ⟨1676597493, 366843329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9699392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19529760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19529760 = ⟨945919187, 692394353⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9764880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20185152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20185152 = ⟨1051193062, 2113106069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10092576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20578336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20578336 = ⟨671694218, 1829575182⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10289168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20972544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20972544 = ⟨430897376, 660937846⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10486272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21626912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21626912 = ⟨607699154, 958090421⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10813456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22020352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22020352 = ⟨1797270122, 627513351⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11010176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22282304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22282304 = ⟨1390148659, 247943412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11141152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22675488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22675488 = ⟨859784269, 928273508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11337744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23593088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23593088 = ⟨939847951, 1229738234⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11796544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23724064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23724064 = ⟨175693929, 822830441⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11862032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24379456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24379456 = ⟨1115834629, 1163942597⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12189728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24772640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24772640 = ⟨1546759873, 1454503330⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12386320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25821216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25821216 = ⟨1192269349, 1059723539⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12910608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26476608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26476608 = ⟨427766117, 849292389⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13238304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26869792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26869792 = ⟨95918307, 1489153540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13434896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27263488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27263488 = ⟨2127614902, 603163187⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13631744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27787392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27787392 = ⟨319458643, 684340940⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13893696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27918368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27918368 = ⟨984629052, 357244651⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13959184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28573760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28573760 = ⟨217786555, 1830444175⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14286880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28966944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28966944 = ⟨697342113, 1900318289⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14483472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30015520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30015520 = ⟨1020573605, 1527677663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15007760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30408960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30408960 = ⟨1056043442, 1420487418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15204480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30670912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30670912 = ⟨1379090732, 1779775964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15335456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31064096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31064096 = ⟨1012018196, 1512478539⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15532048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31981696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31981696 = ⟨304608657, 1295788621⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15990848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32112672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32112672 = ⟨289460532, 1384191446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16056336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32768064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32768064 = ⟨1492563898, 572140408⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16384032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33161248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33161248 = ⟨1767949085, 1788637373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16580624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34865216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34865216 = ⟨765200501, 1311255385⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17432608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36176000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36176000 = ⟨627028385, 1991069985⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18088000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36962368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36962368 = ⟨622901981, 1842075601⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18481184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38797568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38797568 = ⟨1457463176, 567718197⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19398784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39059520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39059520 = ⟨243311883, 1229978427⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19529760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40370304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40370304 = ⟨727712971, 7842349⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20185152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41156672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41156672 = ⟨503950089, 1237234196⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20578336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43253824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43253824 = ⟨246899655, 995842058⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21626912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44040704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44040704 = ⟨777881029, 1738365517⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22020352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44564608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44564608 = ⟨850628282, 795135286⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22282304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45350976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45350976 = ⟨1699156406, 588630391⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22675488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47186176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47186176 = ⟨670245885, 1868603648⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23593088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47448128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47448128 = ⟨939950222, 2068273488⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23724064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48758912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48758912 = ⟨1760392196, 901021229⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24379456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49545280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49545280 = ⟨791205886, 388215895⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24772640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51642432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51642432 = ⟨340235296, 168859141⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25821216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52953216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52953216 = ⟨363069200, 989362679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26476608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53739584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53739584 = ⟨473133348, 294334819⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26869792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54526976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54526976 = ⟨955512264, 573921543⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27263488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55574784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55574784 = ⟨1521178487, 1334772279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27787392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55836736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55836736 = ⟨437158936, 118808524⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27918368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57147520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57147520 = ⟨1560017434, 536544023⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28573760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57933888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57933888 = ⟨1597879487, 938149230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28966944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60031040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60031040 = ⟨1138506761, 1068746113⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30015520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60817920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60817920 = ⟨412194420, 1645420198⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30408960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61341824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61341824 = ⟨1506950956, 1150665395⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30670912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62128192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62128192 = ⟨27803462, 1124948247⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31064096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63963392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63963392 = ⟨1218464597, 1954443810⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31981696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64225344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64225344 = ⟨1586664935, 928392067⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32112672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65536128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65536128 = ⟨1985025693, 842280098⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32768064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66322496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66322496 = ⟨376206613, 1115378039⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33161248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69730432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69730432 = ⟨37745471, 1234696722⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34865216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72352000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72352000 = ⟨1263485688, 1979405071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36176000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73924736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73924736 = ⟨1490398813, 1702908446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36962368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77595136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77595136 = ⟨462364445, 2001442092⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38797568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_78119040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 78119040 = ⟨1444390843, 643203340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39059520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_80740608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 80740608 = ⟨840140912, 992634172⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40370304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_82313344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 82313344 = ⟨937893487, 1230226630⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41156672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_86507648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86507648 = ⟨640504455, 1913433223⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43253824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88081408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88081408 = ⟨665291814, 184778403⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44040704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89129216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89129216 = ⟨1200112909, 1764872809⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44564608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90701952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90701952 = ⟨10484122, 625187589⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45350976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94372352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94372352 = ⟨1940537250, 2089434528⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47186176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94896256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94896256 = ⟨2138570536, 941754679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47448128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_97517824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 97517824 = ⟨872311341, 1197164591⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48758912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_99090560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 99090560 = ⟨368662357, 1107360636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49545280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_103284864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103284864 = ⟨89592993, 865188307⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51642432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105906432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105906432 = ⟨1616053660, 1283716288⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52953216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_107479168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 107479168 = ⟨1495189111, 770460002⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53739584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_111149568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 111149568 = ⟨1177281368, 1017482004⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55574784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_111673472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 111673472 = ⟨942494493, 1206283353⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55836736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_114295040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114295040 = ⟨767419492, 110512775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57147520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115867776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115867776 = ⟨1459730711, 2113376288⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57933888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120062080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120062080 = ⟨789349425, 2122040205⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60031040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121635840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121635840 = ⟨420922661, 1190171598⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60817920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122683648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122683648 = ⟨362598785, 222075235⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61341824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124256384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124256384 = ⟨1326582413, 1527940428⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62128192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_127926784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 127926784 = ⟨1933578089, 1099545655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63963392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_128450688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128450688 = ⟨2051364085, 704370352⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64225344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_131072256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131072256 = ⟨1970152114, 2130601156⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65536128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_132644992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 132644992 = ⟨1046720443, 1751462207⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66322496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_139460864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 139460864 = ⟨945394203, 486377980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69730432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_144704000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 144704000 = ⟨1170720670, 1171999765⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72352000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_147849472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 147849472 = ⟨374834304, 28034640⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73924736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_155190272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 155190272 = ⟨1413092576, 2009537990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77595136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_156238080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 156238080 = ⟨1590599862, 1383635072⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78119040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_161481216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 161481216 = ⟨970779940, 1977320014⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80740608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_164626688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 164626688 = ⟨1958012719, 706991623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82313344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_173015296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 173015296 = ⟨2061990009, 1734524108⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86507648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_178258432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 178258432 = ⟨483623084, 1302280565⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89129216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_181403904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 181403904 = ⟨22245671, 1769562445⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90701952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_188744704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 188744704 = ⟨251387545, 585003076⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94372352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_189792512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 189792512 = ⟨1222806052, 1810709645⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94896256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_195035648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 195035648 = ⟨1088947300, 1595585203⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_97517824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_198181120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 198181120 = ⟨1842688300, 628539584⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99090560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_206569728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 206569728 = ⟨580987958, 839663778⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103284864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_211812864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 211812864 = ⟨1468557990, 269155063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105906432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_214958336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 214958336 = ⟨865746281, 1243249747⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_107479168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_222299136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 222299136 = ⟨1608154088, 833338502⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111149568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_223346944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 223346944 = ⟨933958685, 2061290587⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111673472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_228590080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 228590080 = ⟨2139474615, 1614145844⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114295040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_231735552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 231735552 = ⟨709439332, 2085229015⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115867776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_240124160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 240124160 = ⟨1883998043, 87942155⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120062080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_245367296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 245367296 = ⟨1554263997, 2091289892⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122683648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_248512768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 248512768 = ⟨1714893427, 1543851643⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124256384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_255853568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 255853568 = ⟨1717922210, 1653599957⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_127926784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_256901376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 256901376 = ⟨1109394420, 1812068702⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128450688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_262144512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 262144512 = ⟨1791947754, 1442564829⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131072256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_265289984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 265289984 = ⟨727196913, 1571337965⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_132644992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_278921728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 278921728 = ⟨636410556, 429717159⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_139460864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_289408000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 289408000 = ⟨178995476, 298519990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_144704000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_295698944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 295698944 = ⟨787817156, 1530799394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_147849472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_312476160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 312476160 = ⟨1879676410, 1782855999⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_156238080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_322962432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 322962432 = ⟨661117737, 832530753⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_161481216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_329253376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 329253376 = ⟨1519221412, 1142507905⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_164626688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_346030592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 346030592 = ⟨1512379098, 990370748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_173015296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_356516864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 356516864 = ⟨90485419, 2034131803⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_178258432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_362807808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 362807808 = ⟨1050800180, 2130643167⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_181403904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_379585024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 379585024 = ⟨926319313, 1407055481⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_189792512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_390071296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 390071296 = ⟨746184711, 1733602777⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_195035648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_396362240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 396362240 = ⟨1708176585, 1449578057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_198181120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_413139456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 413139456 = ⟨165284771, 1111195667⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_206569728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_423625728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 423625728 = ⟨424922113, 74654605⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_211812864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_429916672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 429916672 = ⟨934916024, 1251294206⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_214958336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_446693888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 446693888 = ⟨1561389682, 1550102731⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_223346944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_457180160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 457180160 = ⟨661565914, 1221956578⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_228590080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_463471104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 463471104 = ⟨1535909890, 1462214194⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_231735552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_480248320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 480248320 = ⟨852420499, 1210595458⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_240124160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_490734592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 490734592 = ⟨473403782, 542036433⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_245367296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_497025536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 497025536 = ⟨1509318587, 255746224⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_248512768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_513802752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 513802752 = ⟨1584486730, 783523842⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_256901376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_524289024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 524289024 = ⟨742148341, 1117355050⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_262144512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_530579968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 530579968 = ⟨1600405706, 1803119404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_265289984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_557843456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 557843456 = ⟨660937846, 1716586271⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_278921728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_591397888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 591397888 = ⟨573921543, 1191971383⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_295698944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_624952320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 624952320 = ⟨184778403, 1482191833⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_312476160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_658506752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 658506752 = ⟨1190171598, 1726560986⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_329253376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_692061184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 692061184 = ⟨2009537990, 734391071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_346030592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_725615616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 725615616 = ⟨585003076, 1896096102⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_362807808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_759170048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 759170048 = ⟨833338502, 539329559⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_379585024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_792724480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 792724480 = ⟨1653599957, 429561437⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_396362240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_826278912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 826278912 = ⟨298519990, 1968488171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_413139456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_859833344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 859833344 = ⟨832530753, 1486365910⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_429916672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_893387776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 893387776 = ⟨2034131803, 2056998228⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_446693888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_926942208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 926942208 = ⟨1733602777, 1401298936⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_463471104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_960496640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 960496640 = ⟨74654605, 1722561534⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_480248320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_994051072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 994051072 = ⟨1221956578, 1485917733⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_497025536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1027605504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1027605504 = ⟨542036433, 1674079865⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_513802752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1061159936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1061159936 = ⟨1117355050, 1405335306⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_530579968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 160) = ⟨430897376, 660937846⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 160 = 20972544 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_20972544

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨430897376, 660937846⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 160) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 161) = ⟨660937846, 1716586271⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 161 = 557843456 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_557843456

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨660937846, 1716586271⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 161) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 162) = ⟨178995476, 298519990⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 162 = 289408000 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_289408000

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨178995476, 298519990⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 162) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 163) = ⟨298519990, 1968488171⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 163 = 826278912 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_826278912

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨298519990, 1968488171⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 163) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 164) = ⟨1413092576, 2009537990⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 164 = 155190272 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_155190272

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1413092576, 2009537990⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 164) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 165) = ⟨2009537990, 734391071⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 165 = 692061184 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_692061184

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2009537990, 734391071⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 165) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 166) = ⟨424922113, 74654605⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 166 = 423625728 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_423625728

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨424922113, 74654605⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 166) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 167) = ⟨74654605, 1722561534⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 167 = 960496640 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_960496640

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨74654605, 1722561534⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 167) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 168) = ⟨665291814, 184778403⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 168 = 88081408 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_88081408

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨665291814, 184778403⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 168) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 169) = ⟨184778403, 1482191833⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 169 = 624952320 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_624952320

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨184778403, 1482191833⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 169) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 170) = ⟨90485419, 2034131803⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 170 = 356516864 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_356516864

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨90485419, 2034131803⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 170) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 171) = ⟨2034131803, 2056998228⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 171 = 893387776 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_893387776

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2034131803, 2056998228⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 171) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 172) = ⟨1608154088, 833338502⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 172 = 222299136 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_222299136

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1608154088, 833338502⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 172) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 173) = ⟨833338502, 539329559⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 173 = 759170048 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_759170048

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨833338502, 539329559⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 173) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 174) = ⟨473403782, 542036433⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 174 = 490734592 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_490734592

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨473403782, 542036433⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 174) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 175) = ⟨542036433, 1674079865⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 175 = 1027605504 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1027605504

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨542036433, 1674079865⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 175) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 176) = ⟨955512264, 573921543⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 176 = 54526976 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_54526976

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨955512264, 573921543⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 176) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 177) = ⟨573921543, 1191971383⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 177 = 591397888 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_591397888

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨573921543, 1191971383⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 177) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 178) = ⟨661117737, 832530753⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 178 = 322962432 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_322962432

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨661117737, 832530753⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 178) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 179) = ⟨832530753, 1486365910⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 179 = 859833344 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_859833344

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨832530753, 1486365910⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 179) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 180) = ⟨251387545, 585003076⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 180 = 188744704 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_188744704

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨251387545, 585003076⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 180) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 181) = ⟨585003076, 1896096102⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 181 = 725615616 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_725615616

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨585003076, 1896096102⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 181) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 182) = ⟨661565914, 1221956578⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 182 = 457180160 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_457180160

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨661565914, 1221956578⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 182) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 183) = ⟨1221956578, 1485917733⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 183 = 994051072 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_994051072

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1221956578, 1485917733⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 183) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 184) = ⟨420922661, 1190171598⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 184 = 121635840 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_121635840

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨420922661, 1190171598⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 184) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 185) = ⟨1190171598, 1726560986⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 185 = 658506752 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_658506752

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1190171598, 1726560986⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 185) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 186) = ⟨746184711, 1733602777⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 186 = 390071296 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_390071296

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨746184711, 1733602777⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 186) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 187) = ⟨1733602777, 1401298936⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 187 = 926942208 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_926942208

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1733602777, 1401298936⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 187) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 188) = ⟨1717922210, 1653599957⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 188 = 255853568 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_255853568

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1717922210, 1653599957⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 188) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 189) = ⟨1653599957, 429561437⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 189 = 792724480 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_792724480

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1653599957, 429561437⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 189) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 190) = ⟨742148341, 1117355050⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 190 = 524289024 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_524289024

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨742148341, 1117355050⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 190) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 191) = ⟨1117355050, 1405335306⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 191 = 1061159936 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1061159936

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1117355050, 1405335306⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 191) := by
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

end R17TableAChunk05Certificate
