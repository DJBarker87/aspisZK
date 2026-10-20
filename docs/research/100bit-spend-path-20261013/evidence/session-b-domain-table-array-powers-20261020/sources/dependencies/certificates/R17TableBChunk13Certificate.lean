import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableBChunk13Certificate
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

theorem power_44 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44 = ⟨621742329, 545390881⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22]
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

theorem power_82 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 82 = ⟨588340926, 1971636517⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41]
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

theorem power_88 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88 = ⟨611478089, 464063968⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44]
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

theorem power_106 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106 = ⟨382757218, 311908650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_107 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 107 = ⟨1286380731, 398286559⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108 = ⟨467798412, 1281237586⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54]
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

theorem power_133 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 133 = ⟨697736105, 1609499589⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_139 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 139 = ⟨1724704064, 760534735⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_141 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 141 = ⟨1089936147, 199619290⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_149 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 149 = ⟨1021562393, 1112546712⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_150 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 150 = ⟨141696057, 732771971⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_155 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 155 = ⟨95599379, 1884941993⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_157 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 157 = ⟨136913421, 2042158206⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_165 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 165 = ⟨1912338015, 1472102703⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_171 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 171 = ⟨617956980, 1693803782⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_172 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 172 = ⟨1271351363, 2142894890⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_173 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 173 = ⟨172481178, 435324837⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 176 = ⟨1326093758, 824702110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_181 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 181 = ⟨1696217250, 537553639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_182 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 182 = ⟨2049618010, 1067206337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_187 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 187 = ⟨799610937, 665210564⟩ := by
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

theorem power_203 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 203 = ⟨1626325386, 533448899⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_205 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 205 = ⟨1921054693, 699847975⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_213 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 213 = ⟨1005480520, 1074898100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_214 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 214 = ⟨1649714937, 2053196164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_107]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 216 = ⟨1396449152, 728546296⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_219 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 219 = ⟨742915033, 302287293⟩ := by
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

theorem power_235 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 235 = ⟨1800142309, 2130869144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_236 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 236 = ⟨1882349838, 1929949081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_237 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 237 = ⟨1434289749, 1293959886⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_245 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 245 = ⟨58842794, 1641594984⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_246 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 246 = ⟨1542475593, 236234992⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_251 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 251 = ⟨1126878156, 83731982⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_253 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 253 = ⟨1147263237, 1829594721⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_267 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 267 = ⟨437947673, 1533647995⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_278 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 278 = ⟨2075577012, 158471336⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_139]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_283 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 283 = ⟨295176368, 201131562⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_141]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_299 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 299 = ⟨416565636, 1037762693⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_149]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_300 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 300 = ⟨1826511843, 427717874⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_150]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_310 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 310 = ⟨1522755374, 386473027⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_155]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_315 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 315 = ⟨1081072330, 2017659140⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_157]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_331 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 331 = ⟨32296809, 2102726368⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_165]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_342 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 342 = ⟨1980366618, 934891035⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_171]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 344 = ⟨920191220, 656982226⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_172]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_347 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 347 = ⟨925168958, 1293579781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_173]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 352 = ⟨2122028404, 1461483964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_363 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 363 = ⟨1651768743, 584734852⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_181]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_364 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 364 = ⟨658152473, 1072395370⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_182]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_374 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 374 = ⟨2056754104, 1797437257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_187]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_379 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 379 = ⟨248266738, 822733905⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_189]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_395 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 395 = ⟨168348602, 731130525⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_197]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_406 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 406 = ⟨1993180049, 1487749769⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_203]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_411 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 411 = ⟨1461501571, 320981148⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_205]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_427 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 427 = ⟨49575956, 403696603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_213]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_428 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 428 = ⟨1605594036, 1195313748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_214]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 432 = ⟨2080418350, 1727780629⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_438 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 438 = ⟨585484066, 1561821963⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_219]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_443 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 443 = ⟨79760015, 1466610042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_221]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_459 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 459 = ⟨781696041, 857406122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_229]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_470 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 470 = ⟨266031331, 1924825944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_235]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 472 = ⟨1631040737, 1802692420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_236]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_475 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 475 = ⟨472398784, 1073235775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_237]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_491 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 491 = ⟨122141927, 528602653⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_245]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_492 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 492 = ⟨1391406444, 1044822016⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_246]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_502 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 502 = ⟨1490553968, 258980480⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_251]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_507 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 507 = ⟨64356432, 562208444⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_253]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_534 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 534 = ⟨542553737, 457499144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_267]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_556 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 556 = ⟨268812888, 841508424⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_278]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_566 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 566 = ⟨1735204805, 896977394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_283]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_598 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 598 = ⟨958074729, 342601689⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_299]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 600 = ⟨1183830334, 1283287492⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_300]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_620 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 620 = ⟨1678507858, 1723938487⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_310]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_630 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 630 = ⟨758237145, 1068647096⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_315]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_662 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 662 = ⟨1196737752, 244942799⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_331]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_684 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 684 = ⟨633764744, 1139409834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_342]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 688 = ⟨1246945925, 1128446404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_694 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 694 = ⟨1078137057, 411959343⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_347]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 704 = ⟨1130890301, 1314091057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_726 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 726 = ⟨237965545, 1477043771⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_363]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 728 = ⟨152082636, 622063853⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_364]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_748 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 748 = ⟨1533866668, 2042313092⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_374]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_758 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 758 = ⟨1723722072, 562123638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_379]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_790 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 790 = ⟨1293141798, 1132989962⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_395]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_812 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 812 = ⟨674748761, 1180944676⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_406]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_822 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 822 = ⟨2138022126, 1048929303⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_411]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_854 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 854 = ⟨1560834164, 909022063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_427]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 856 = ⟨1428851677, 390729132⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_428]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 864 = ⟨1921307644, 464663069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_876 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 876 = ⟨1585126802, 1483382865⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_438]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_886 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 886 = ⟨1215651670, 1870800270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_443]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_918 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 918 = ⟨524288858, 1888389253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_459]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_940 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 940 = ⟨869208073, 769182738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_470]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 944 = ⟨144926793, 2141311607⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_950 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 950 = ⟨4681106, 219594385⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_475]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_982 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 982 = ⟨1809855132, 1819706569⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_491]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 984 = ⟨2061938011, 1225693194⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_492]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1004 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1004 = ⟨1988779399, 1219292293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_502]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1014 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1014 = ⟨1270549912, 1039491549⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_507]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1068 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1068 = ⟨1555912358, 205828074⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_534]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1112 = ⟨1509285423, 1110052489⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_556]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1132 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1132 = ⟨1451922308, 406175824⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_566]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1196 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1196 = ⟨958083333, 720386296⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_598]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1200 = ⟨2053141228, 12472555⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1240 = ⟨465988776, 186828766⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_620]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1260 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1260 = ⟨1846825890, 123342395⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_630]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1324 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1324 = ⟨2042065285, 1026018915⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_662]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1368 = ⟨1514395361, 2134321615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_684]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1376 = ⟨1771456860, 1392465920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1388 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1388 = ⟨1850487690, 451145199⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_694]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1408 = ⟨105012991, 261334420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1452 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1452 = ⟨1752998435, 268001355⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_726]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1456 = ⟨447640678, 314692891⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1496 = ⟨1626198703, 429410477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_748]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1516 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1516 = ⟨640821202, 1826338359⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_758]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1580 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1580 = ⟨1777586327, 2097694307⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_790]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1624 = ⟨1926365772, 1981066635⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_812]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1644 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1644 = ⟨752649197, 395483634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_822]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1708 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1708 = ⟨143126798, 115970012⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_854]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1712 = ⟨1462802781, 1948399774⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1728 = ⟨1136461567, 2028297119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1752 = ⟨1458004538, 239986594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_876]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1772 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1772 = ⟨574803850, 895191472⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_886]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1836 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1836 = ⟨22592141, 719370770⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_918]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1880 = ⟨890167323, 687452307⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_940]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1888 = ⟨269305067, 1242485321⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1900 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1900 = ⟨1807982142, 11891464⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_950]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1964 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1964 = ⟨1003968700, 417493903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_982]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1968 = ⟨1305669901, 1881194309⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2008 = ⟨855514728, 1815742830⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1004]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2028 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2028 = ⟨858660623, 1065569602⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1014]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2136 = ⟨1128427657, 277898188⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1068]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2224 = ⟨1745525696, 769760567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2264 = ⟨329732256, 1766250655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1132]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2392 = ⟨1742098191, 1037130408⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1196]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2400 = ⟨321804958, 211969623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2480 = ⟨1879715677, 2055657011⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2520 = ⟨110807802, 756114145⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1260]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2648 = ⟨1484067135, 1265132893⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1324]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2736 = ⟨1133836227, 2057567625⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2752 = ⟨937276350, 1889866233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2776 = ⟨917952685, 650740977⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1388]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2816 = ⟨638925477, 1200786367⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2904 = ⟨2076615481, 1321965726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1452]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2912 = ⟨1514720099, 1344022831⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2992 = ⟨497029902, 1283766712⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3032 = ⟨1866401566, 1282373582⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1516]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3160 = ⟨1017583464, 387174195⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1580]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3248 = ⟨929654382, 1189184447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3288 = ⟨370868227, 125089907⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1644]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3416 = ⟨10606219, 2103170239⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1708]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3424 = ⟨541646190, 100709305⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3456 = ⟨1696585972, 468920631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3504 = ⟨985269965, 309158862⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3544 = ⟨958934792, 1789617746⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1772]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3672 = ⟨1170842664, 1530270903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1836]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3760 = ⟨373501011, 1773718357⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3776 = ⟨1759380646, 1693051226⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3800 = ⟨1174248721, 1094917836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1900]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3928 = ⟨1560769618, 1468172236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1964]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3936 = ⟨993869978, 1660964583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4016 = ⟨479859971, 232817279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4056 = ⟨2000611453, 10186879⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2028]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4272 = ⟨585610041, 1618324184⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4448 = ⟨1017551858, 1236182754⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4528 = ⟨441570631, 968386700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4784 = ⟨1467294171, 430456315⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4800 = ⟨1333172839, 2105072738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4960 = ⟨2083665654, 991547815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5040 = ⟨471692473, 2103104893⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5296 = ⟨599892114, 2048112721⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5472 = ⟨1038155407, 654032931⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5504 = ⟨558010101, 1952904556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5552 = ⟨1099391448, 1351169608⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5632 = ⟨1739299167, 1982296282⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5808 = ⟨1138569545, 1540293249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5824 = ⟨1240031076, 1183521928⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5984 = ⟨193776427, 193013472⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6064 = ⟨1263283658, 586019404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6320 = ⟨1361228960, 565990865⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6496 = ⟨376013865, 14021834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6576 = ⟨283548535, 1536268119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6832 = ⟨491190319, 1122196136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6848 = ⟨722953962, 973016167⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6912 = ⟨900851131, 714016362⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7008 = ⟨1107806556, 337654334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7088 = ⟨1230212480, 1999380932⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7344 = ⟨1279250882, 1548001106⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7520 = ⟨100383435, 1123913136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7552 = ⟨198166676, 739745441⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7600 = ⟨1215987181, 491211212⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7856 = ⟨1374060404, 2131475800⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7872 = ⟨1647829762, 864777955⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8032 = ⟨1869824360, 2007729881⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8112 = ⟨697026681, 1683466747⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8544 = ⟨934738593, 1740365254⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8896 = ⟨1395128231, 1865727046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9056 = ⟨873290061, 311930335⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9568 = ⟨416525597, 710044375⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9600 = ⟨1859245018, 579400817⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9920 = ⟨416032040, 436061717⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10080 = ⟨1251880721, 1814382040⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10592 = ⟨1840232436, 960076528⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10944 = ⟨1989420027, 796334698⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11008 = ⟨1905939861, 629388659⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11104 = ⟨1367533983, 85188912⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11264 = ⟨226985029, 1154128883⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11616 = ⟨1996761418, 1427690425⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11648 = ⟨1954706102, 753082980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11968 = ⟨379588099, 2015219960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12128 = ⟨14167238, 1424589678⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12640 = ⟨1522447366, 1013044512⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12992 = ⟨2073155059, 1861723544⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13152 = ⟨888221515, 1461740638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13664 = ⟨771936478, 1369045713⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13696 = ⟨601495200, 1068716428⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13824 = ⟨2122891308, 1958068349⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14016 = ⟨1727218271, 1378950967⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14176 = ⟨1919911903, 2130024251⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14688 = ⟨227311576, 1819204462⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15040 = ⟨21654848, 1835385374⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15104 = ⟨1798126249, 1236021248⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15200 = ⟨2042568855, 195565630⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15712 = ⟨1083656674, 1429557910⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15744 = ⟨1326215179, 1403584070⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16064 = ⟨1247842032, 2066924212⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16224 = ⟨1069472905, 304885984⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17088 = ⟨823540843, 726250012⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17792 = ⟨1224155440, 737054196⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18112 = ⟨474412599, 1978188843⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19136 = ⟨257812610, 2045226232⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19200 = ⟨577643380, 209794086⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19840 = ⟨65328010, 639240918⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20160 = ⟨1111872017, 558824191⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21184 = ⟨1401548331, 126202720⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21888 = ⟨1648413638, 1061699244⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22016 = ⟨90637269, 952277332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22208 = ⟨1496190116, 433235339⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22528 = ⟨286695904, 1021278776⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23232 = ⟨390401177, 1613978388⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23296 = ⟨479665279, 2094867031⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23936 = ⟨419971577, 335850108⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24256 = ⟨736898165, 1763962282⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25280 = ⟨1605071575, 426278271⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25984 = ⟨314467329, 1076108506⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26304 = ⟨1135655347, 1659108092⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27328 = ⟨215420262, 9496034⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27392 = ⟨689256424, 1078534379⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27648 = ⟨405776385, 918871706⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28032 = ⟨817446573, 1865300049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28352 = ⟨1000079081, 1233807271⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29376 = ⟨185488607, 1007549772⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30080 = ⟨793102838, 1371236975⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30208 = ⟨422667070, 645353689⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30400 = ⟨780738596, 621590161⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31424 = ⟨1024282732, 506600347⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31488 = ⟨1506146295, 15201801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32128 = ⟨1577983544, 1968787947⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32448 = ⟨1311604223, 1172767148⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34176 = ⟨1928510894, 823884280⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35584 = ⟨1896519407, 1492919974⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36224 = ⟨1111614911, 1721991295⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38272 = ⟨2129679054, 306337777⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38400 = ⟨733453396, 414961443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39680 = ⟨1903571649, 1433527792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40320 = ⟨531896240, 1815837487⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42368 = ⟨1077862772, 1728208146⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43776 = ⟨1363012592, 1582066627⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44032 = ⟨1331567834, 835563095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44416 = ⟨593741418, 492348622⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45056 = ⟨1984370174, 548484416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46464 = ⟨447173230, 565116145⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46592 = ⟨1589750714, 89434798⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47872 = ⟨787168508, 926614792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48512 = ⟨956669494, 169987736⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50560 = ⟨1887381850, 1290605153⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51968 = ⟨2123816611, 1161003328⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52608 = ⟨1698714399, 917041418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54656 = ⟨648184043, 2089367060⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54784 = ⟨719993641, 1182977325⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55296 = ⟨643989886, 49445127⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56064 = ⟨802977795, 1098240563⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56704 = ⟨1534556761, 1180232104⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58752 = ⟨519513315, 357106852⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60160 = ⟨1187724674, 1065852279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60416 = ⟨173326764, 1317620144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60800 = ⟨1459113504, 928652754⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62848 = ⟨850706226, 336868663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62976 = ⟨513154727, 1233224454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64256 = ⟨1838928993, 2087714324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64896 = ⟨986778485, 364021437⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_68352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 68352 = ⟨293150961, 612708306⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71168 = ⟨184241407, 1379835763⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72448 = ⟨787658421, 1386036871⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76544 = ⟨1171720193, 657660264⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76800 = ⟨1291436019, 379698066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_79360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79360 = ⟨891168903, 1145658271⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_80640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 80640 = ⟨1930863542, 1403072932⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_84736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84736 = ⟨905460175, 2111671947⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87552 = ⟨986053408, 1438909564⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88064 = ⟨1629336806, 1209471979⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88832 = ⟨723125335, 1206213842⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92928 = ⟨121042675, 283175388⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_93184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93184 = ⟨2140616907, 88929576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_95744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 95744 = ⟨1287895149, 733680821⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_97024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 97024 = ⟨1788045589, 1279117263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_101120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101120 = ⟨1639052459, 705279619⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_103936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103936 = ⟨866756571, 1940004712⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105216 = ⟨1630110338, 145778879⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_109312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109312 = ⟨1946305829, 108721921⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_109568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109568 = ⟨1845927943, 1778670715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_110592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110592 = ⟨854984042, 63484416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_112128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112128 = ⟨1386244047, 812565330⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_113408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 113408 = ⟨19302619, 926963417⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_117504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117504 = ⟨1571860358, 932235031⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120320 = ⟨875923454, 1002878540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120832 = ⟨947160035, 834918877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121600 = ⟨1641946451, 1791706455⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125696 = ⟨308524219, 1619876320⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125952 = ⟨895303357, 1473739262⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_128512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128512 = ⟨721805400, 1392862222⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_129792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 129792 = ⟨690493060, 1699614655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_136704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 136704 = ⟨1491305601, 825559218⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_142336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 142336 = ⟨4665041, 1024239759⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_144896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 144896 = ⟨463746829, 1595454020⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_153088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 153088 = ⟨1142070205, 1735622340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_153600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 153600 = ⟨1507456974, 2049594119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_158720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 158720 = ⟨70447031, 2045853490⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_161280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 161280 = ⟨1860693792, 620537785⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_169472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 169472 = ⟨901680448, 1530532110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_175104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 175104 = ⟨556319643, 929512182⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_176128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 176128 = ⟨591304555, 68989614⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_177664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 177664 = ⟨1417980809, 534706983⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_185856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 185856 = ⟨1313344138, 2133188641⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_186368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 186368 = ⟨1787064488, 51350066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_191488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 191488 = ⟨1105783134, 1665513152⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_95744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_194048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 194048 = ⟨737810191, 314213371⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_97024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_202240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 202240 = ⟨1035612393, 339027763⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_207872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 207872 = ⟨1209995250, 553854041⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_210432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 210432 = ⟨1004176014, 1441488760⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_218624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 218624 = ⟨818555245, 2020936403⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_219136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 219136 = ⟨232802090, 2145208109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_224256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 224256 = ⟨2086473419, 1632839764⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_226816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 226816 = ⟨1080042027, 1606774010⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_113408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_235008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 235008 = ⟨1649957420, 1656333801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_240640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 240640 = ⟨963307978, 1053907585⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_241664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 241664 = ⟨1696657789, 2121958423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_243200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 243200 = ⟨541597073, 565666698⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_251392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 251392 = ⟨767275567, 1944222165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_251904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 251904 = ⟨2044929748, 722179404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_257024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 257024 = ⟨1291854463, 1462274122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_259584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 259584 = ⟨1089297940, 1040877436⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_129792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_273408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 273408 = ⟨1579902773, 1483615572⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_136704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_284672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 284672 = ⟨16505965, 987006001⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_142336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_289792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 289792 = ⟨820863262, 760069938⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_144896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_306176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 306176 = ⟨588014444, 2107854929⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_153088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_307200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 307200 = ⟨207319829, 330698049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_153600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_317440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 317440 = ⟨2016210977, 309319334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_158720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_322560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 322560 = ⟨376051332, 1816897189⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_161280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_338944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 338944 = ⟨520155465, 2100668121⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_169472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_350208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 350208 = ⟨1761157983, 1349037604⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_175104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_355328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 355328 = ⟨1879962606, 1115530419⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_177664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_371712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 371712 = ⟨1809715087, 1416462409⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_185856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_372736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 372736 = ⟨787391422, 234435571⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_186368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_382976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 382976 = ⟨1511581357, 1880607053⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_191488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_388096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 388096 = ⟨1224164865, 1521291625⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_194048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_404480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 404480 = ⟨123826954, 252571166⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_202240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_415744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 415744 = ⟨1283093627, 1257551079⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_207872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_420864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 420864 = ⟨1490212935, 382606885⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_210432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_437248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 437248 = ⟨849472906, 569578799⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_218624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_438272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 438272 = ⟨1167250594, 1854887903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_219136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_448512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 448512 = ⟨1113246356, 1550960305⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_224256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_453632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 453632 = ⟨174045998, 958024763⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_226816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_470016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 470016 = ⟨858062143, 73231491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_235008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_481280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 481280 = ⟨2098579920, 1448151653⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_240640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_486400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 486400 = ⟨1513932564, 1290647036⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_243200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_502784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 502784 = ⟨1175249482, 814877247⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_251392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_503808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 503808 = ⟨2077839401, 709133143⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_251904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_514048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 514048 = ⟨837830915, 726127712⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_257024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_519168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 519168 = ⟨1762889636, 128769293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_259584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_546816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 546816 = ⟨224591501, 846079997⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_273408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_569344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 569344 = ⟨1997990904, 355093967⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_284672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_579584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 579584 = ⟨305070376, 1850936260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_289792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_612352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 612352 = ⟨346749507, 1146096656⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_306176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_634880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 634880 = ⟨450129036, 2130393939⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_317440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_645120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 645120 = ⟨913278836, 825866966⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_322560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_677888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 677888 = ⟨836368227, 929402528⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_338944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_700416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 700416 = ⟨865056590, 1396323689⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_350208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_710656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 710656 = ⟨560216916, 1994550783⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_355328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_743424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 743424 = ⟨1136241220, 977658468⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_371712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_765952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 765952 = ⟨1735177288, 1041858071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_382976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_776192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 776192 = ⟨1163210980, 1792973190⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_388096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_808960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 808960 = ⟨1533402706, 1232994447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_404480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_831488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 831488 = ⟨1608197410, 953495473⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_415744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_841728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 841728 = ⟨833507523, 2106438492⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_420864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_874496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 874496 = ⟨1074280865, 1262856891⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_437248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_897024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 897024 = ⟨92769725, 1231653419⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_448512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_907264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 907264 = ⟨464450103, 702356776⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_453632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_940032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 940032 = ⟨1163539454, 147541701⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_470016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_962560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 962560 = ⟨719959488, 88680757⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_481280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_972800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 972800 = ⟨2006670527, 11111793⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_486400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1005568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1005568 = ⟨983149665, 227977919⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_502784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1028096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1028096 = ⟨1742529025, 278083478⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_514048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1038336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1038336 = ⟨40204141, 2063053276⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_519168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1093632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1093632 = ⟨1760363481, 2129820178⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_546816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1159168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1159168 = ⟨512573355, 559650698⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_579584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1224704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1224704 = ⟨569540672, 885330917⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_612352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1290240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1290240 = ⟨181669902, 1993442275⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_645120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1355776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1355776 = ⟨480315830, 137067372⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_677888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1421312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1421312 = ⟨808165703, 1317710352⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_710656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1486848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1486848 = ⟨112696124, 268389163⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_743424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1552384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1552384 = ⟨479770865, 2027287932⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_776192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1617920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1617920 = ⟨1980954341, 561676940⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_808960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1683456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1683456 = ⟨934129539, 1082077994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_841728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1748992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1748992 = ⟨237150930, 715611246⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_874496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1814528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1814528 = ⟨265914936, 748543764⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_907264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1880064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1880064 = ⟨1433755461, 316564196⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_940032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1945600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1945600 = ⟨1699669774, 817702196⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_972800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2011136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2011136 = ⟨498135791, 1918711876⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1005568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2076672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2076672 = ⟨1334313253, 1249554241⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1038336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 416) = ⟨1984370174, 548484416⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 416 = 45056 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_45056

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1984370174, 548484416⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 416) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 417) = ⟨1760363481, 2129820178⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 417 = 1093632 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1093632

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1760363481, 2129820178⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 417) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 418) = ⟨1997990904, 355093967⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 418 = 569344 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_569344

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1997990904, 355093967⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 418) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 419) = ⟨1980954341, 561676940⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 419 = 1617920 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1617920

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1980954341, 561676940⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 419) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 420) = ⟨207319829, 330698049⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 420 = 307200 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_307200

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨207319829, 330698049⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 420) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 421) = ⟨480315830, 137067372⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 421 = 1355776 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1355776

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨480315830, 137067372⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 421) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 422) = ⟨1608197410, 953495473⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 422 = 831488 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_831488

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1608197410, 953495473⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 422) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 423) = ⟨1433755461, 316564196⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 423 = 1880064 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1880064

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1433755461, 316564196⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 423) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 424) = ⟨591304555, 68989614⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 424 = 176128 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_176128

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨591304555, 68989614⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 424) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 425) = ⟨569540672, 885330917⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 425 = 1224704 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1224704

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨569540672, 885330917⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 425) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 426) = ⟨865056590, 1396323689⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 426 = 700416 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_700416

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨865056590, 1396323689⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 426) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 427) = ⟨237150930, 715611246⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 427 = 1748992 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1748992

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨237150930, 715611246⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 427) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 428) = ⟨1167250594, 1854887903⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 428 = 438272 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_438272

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1167250594, 1854887903⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 428) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 429) = ⟨112696124, 268389163⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 429 = 1486848 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1486848

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨112696124, 268389163⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 429) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 430) = ⟨719959488, 88680757⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 430 = 962560 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_962560

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨719959488, 88680757⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 430) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 431) = ⟨498135791, 1918711876⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 431 = 2011136 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2011136

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨498135791, 1918711876⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 431) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 432) = ⟨854984042, 63484416⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 432 = 110592 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_110592

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨854984042, 63484416⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 432) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 433) = ⟨512573355, 559650698⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 433 = 1159168 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1159168

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨512573355, 559650698⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 433) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 434) = ⟨450129036, 2130393939⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 434 = 634880 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_634880

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨450129036, 2130393939⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 434) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 435) = ⟨934129539, 1082077994⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 435 = 1683456 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1683456

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨934129539, 1082077994⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 435) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 436) = ⟨787391422, 234435571⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 436 = 372736 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_372736

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨787391422, 234435571⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 436) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 437) = ⟨808165703, 1317710352⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 437 = 1421312 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1421312

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨808165703, 1317710352⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 437) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 438) = ⟨92769725, 1231653419⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 438 = 897024 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_897024

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨92769725, 1231653419⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 438) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 439) = ⟨1699669774, 817702196⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 439 = 1945600 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1945600

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1699669774, 817702196⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 439) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 440) = ⟨1696657789, 2121958423⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 440 = 241664 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_241664

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1696657789, 2121958423⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 440) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 441) = ⟨181669902, 1993442275⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 441 = 1290240 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1290240

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨181669902, 1993442275⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 441) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 442) = ⟨1735177288, 1041858071⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 442 = 765952 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_765952

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1735177288, 1041858071⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 442) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 443) = ⟨265914936, 748543764⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 443 = 1814528 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1814528

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨265914936, 748543764⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 443) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 444) = ⟨2077839401, 709133143⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 444 = 503808 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_503808

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2077839401, 709133143⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 444) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 445) = ⟨479770865, 2027287932⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 445 = 1552384 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1552384

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨479770865, 2027287932⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 445) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 446) = ⟨1742529025, 278083478⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 446 = 1028096 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1028096

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1742529025, 278083478⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 446) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 447) = ⟨1334313253, 1249554241⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 447 = 2076672 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2076672

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1334313253, 1249554241⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 447) := by
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

end R17TableBChunk13Certificate
