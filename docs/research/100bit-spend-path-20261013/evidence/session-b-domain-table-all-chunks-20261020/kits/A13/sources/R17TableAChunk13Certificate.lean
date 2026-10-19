import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk13Certificate
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

theorem power_22529 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22529 = ⟨1278488550, 855202992⟩ := by
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

theorem power_45058 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45058 = ⟨2005442967, 206363411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22529]
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

theorem power_55297 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55297 = ⟨507119747, 1601750247⟩ := by
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

theorem power_88065 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88065 = ⟨52199796, 915988870⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88832 = ⟨723125335, 1206213842⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90116 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90116 = ⟨1344260796, 862027809⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45058]
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

theorem power_110594 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110594 = ⟨764379819, 1269506779⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55297]
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

theorem power_120833 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120833 = ⟨2116744384, 1765815319⟩ := by
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

theorem power_153601 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 153601 = ⟨936709977, 1893123199⟩ := by
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

theorem power_176130 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 176130 = ⟨366146036, 164424020⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88065]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_177664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 177664 = ⟨1417980809, 534706983⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_180232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 180232 = ⟨1484390080, 1035578014⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90116]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_185856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 185856 = ⟨1313344138, 2133188641⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_186369 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 186369 = ⟨782869813, 486228890⟩ := by
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

theorem power_219137 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 219137 = ⟨1133056873, 1030994715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_221188 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 221188 = ⟨1474776574, 177143284⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110594]
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

theorem power_241666 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 241666 = ⟨1790337161, 1319306673⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120833]
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

theorem power_251905 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 251905 = ⟨501454301, 854220320⟩ := by
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

theorem power_284673 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 284673 = ⟨1678172017, 720801384⟩ := by
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

theorem power_307202 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 307202 = ⟨1119883660, 270645505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_153601]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_317441 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 317441 = ⟨106873017, 201592094⟩ := by
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

theorem power_350209 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 350209 = ⟨905584335, 854476477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_175104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_352260 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 352260 = ⟨1231800110, 387217946⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_176130]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_355328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 355328 = ⟨1879962606, 1115530419⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_177664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_360464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 360464 = ⟨408126747, 1136814162⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_180232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_371712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 371712 = ⟨1809715087, 1416462409⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_185856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_372738 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 372738 = ⟨1328830747, 329510057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_186369]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_382977 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 382977 = ⟨937168107, 1036190176⟩ := by
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

theorem power_415745 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 415745 = ⟨278040551, 1634536686⟩ := by
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

theorem power_438274 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 438274 = ⟨1123657820, 1014252646⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_219137]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_442376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 442376 = ⟨1896460297, 761086562⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_221188]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_448513 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 448513 = ⟨947711388, 2012926299⟩ := by
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

theorem power_481281 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 481281 = ⟨244345395, 439109815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_240640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_483332 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 483332 = ⟨1750350365, 495644437⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_241666]
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

theorem power_503810 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 503810 = ⟨1833396909, 2126447717⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_251905]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_514049 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 514049 = ⟨650589896, 496087646⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_257024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_519168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 519168 = ⟨1762889636, 128769293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_259584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_546817 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 546817 = ⟨1183490836, 1929135917⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_273408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_569346 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 569346 = ⟨620337856, 701023087⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_284673]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_579585 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 579585 = ⟨2077871286, 1585701561⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_289792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_612353 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 612353 = ⟨1495563665, 521659697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_306176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_614404 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 614404 = ⟨1275473337, 902278008⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_307202]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_634882 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 634882 = ⟨176577484, 2093097144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_317441]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_645121 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 645121 = ⟨1491698023, 1963744683⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_322560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_677889 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 677889 = ⟨1436232807, 1689263309⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_338944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_700418 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 700418 = ⟨2038983496, 1275268995⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_350209]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_704520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 704520 = ⟨51620969, 560367278⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_352260]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_710657 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 710657 = ⟨1928210513, 179267783⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_355328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_720928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 720928 = ⟨1387082371, 1783925110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_360464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_743425 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 743425 = ⟨1543495385, 421746617⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_371712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_745476 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 745476 = ⟨1509750909, 706205263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_372738]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_765954 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 765954 = ⟨232712766, 1528455594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_382977]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_776193 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 776193 = ⟨2104720228, 1744526110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_388096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_808961 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 808961 = ⟨2070562716, 623116704⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_404480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_831490 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 831490 = ⟨755653750, 1072797844⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_415745]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_841729 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 841729 = ⟨1977572122, 224209072⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_420864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_874497 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 874497 = ⟨1851616875, 614474218⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_437248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_876548 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 876548 = ⟨158890817, 1929823035⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_438274]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_884752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 884752 = ⟨1594030009, 1792602621⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_442376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_897026 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 897026 = ⟨1227882956, 727666559⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_448513]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_907265 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 907265 = ⟨729382946, 1451564443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_453632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_940033 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 940033 = ⟨1019331040, 768391937⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_470016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_962562 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 962562 = ⟨1982660773, 1907442659⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_481281]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_966664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 966664 = ⟨713325129, 1270895729⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_483332]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_972801 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 972801 = ⟨1988231526, 804696233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_486400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1005569 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1005569 = ⟨1773931419, 1710579986⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_502784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1007620 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1007620 = ⟨258671841, 1212176171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_503810]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1028098 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1028098 = ⟨1154545061, 1928652573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_514049]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1038337 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1038337 = ⟨316363503, 1203167895⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_519168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1093634 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1093634 = ⟨547709996, 290418650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_546817]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1138692 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1138692 = ⟨1668529040, 911775375⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_569346]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1159170 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1159170 = ⟨405353175, 1868977222⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_579585]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1224706 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1224706 = ⟨1021798987, 1106931884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_612353]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1228808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1228808 = ⟨1677446289, 1986023474⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_614404]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1269764 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1269764 = ⟨1454402527, 231420867⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_634882]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1290242 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1290242 = ⟨961767088, 1513866260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_645121]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1355778 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1355778 = ⟨1465698574, 411675544⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_677889]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1400836 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1400836 = ⟨1504936177, 842533616⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_700418]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1409040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1409040 = ⟨59532375, 1048796534⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_704520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1421314 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1421314 = ⟨273594655, 888320921⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_710657]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1441856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1441856 = ⟨1624802358, 1125046099⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_720928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1486850 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1486850 = ⟨2094385297, 1455445174⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_743425]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1490952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1490952 = ⟨555504918, 1597497462⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_745476]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1531908 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1531908 = ⟨1320969628, 367575842⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_765954]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1552386 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1552386 = ⟨1955227775, 984912265⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_776193]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1617922 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1617922 = ⟨7143902, 484940625⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_808961]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1662980 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1662980 = ⟨1290575994, 955466201⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_831490]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1683458 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1683458 = ⟨277261791, 1293309377⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_841729]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1748994 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1748994 = ⟨2030957927, 908993480⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_874497]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1753096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1753096 = ⟨905302650, 660558750⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_876548]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1769504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1769504 = ⟨1178719986, 1024913720⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_884752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1794052 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1794052 = ⟨1555569979, 1304358856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_897026]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1814530 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1814530 = ⟨907293662, 1648528884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_907265]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1880066 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1880066 = ⟨114597403, 1933269810⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_940033]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1925124 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1925124 = ⟨104523448, 37636499⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_962562]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1933328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1933328 = ⟨799163482, 1594286407⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_966664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1945602 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1945602 = ⟨1118066310, 912940167⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_972801]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2011138 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2011138 = ⟨319589963, 207437401⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1005569]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2015240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2015240 = ⟨1746041022, 2100066071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1007620]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2056196 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2056196 = ⟨1235823856, 1691023386⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1028098]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2076674 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2076674 = ⟨1025393795, 270468202⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1038337]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2187268 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2187268 = ⟨544988852, 982070977⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1093634]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2277384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2277384 = ⟨1948401549, 1116445241⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1138692]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2318340 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2318340 = ⟨1326211527, 1598487354⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1159170]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2449412 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2449412 = ⟨149786626, 1128124396⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1224706]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2457616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2457616 = ⟨2009969613, 1071988940⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1228808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2539528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2539528 = ⟨496263355, 672678742⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1269764]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2580484 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2580484 = ⟨1912237463, 272129132⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1290242]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2711556 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2711556 = ⟨1060029098, 625093855⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1355778]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2801672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2801672 = ⟨1168702422, 175595778⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1400836]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2818080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2818080 = ⟨1630177408, 517275636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1409040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2842628 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2842628 = ⟨1839948005, 957640422⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1421314]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2883712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2883712 = ⟨1364975591, 433688223⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1441856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2973700 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2973700 = ⟨542701458, 978240069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1486850]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2981904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2981904 = ⟨1532002320, 800843534⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1490952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3063816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3063816 = ⟨1271287905, 1250611655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1531908]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3104772 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3104772 = ⟨727565346, 1879175914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1552386]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3235844 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3235844 = ⟨773829297, 873676232⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1617922]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3325960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3325960 = ⟨1200020554, 1588949205⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1662980]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3366916 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3366916 = ⟨995803866, 1992560094⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1683458]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3497988 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3497988 = ⟨1348561371, 40413110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1748994]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3506192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3506192 = ⟨1251973395, 94967359⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1753096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3539008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3539008 = ⟨870007668, 1009360430⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1769504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3588104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3588104 = ⟨1721777379, 2021128019⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1794052]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3629060 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3629060 = ⟨1209435886, 1629788004⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1814530]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3760132 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3760132 = ⟨91573679, 36918882⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1880066]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3850248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3850248 = ⟨2000259574, 1620168382⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1925124]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3866656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3866656 = ⟨1673776917, 1863981635⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1933328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3891204 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3891204 = ⟨1732326583, 1327823581⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1945602]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4022276 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4022276 = ⟨367659748, 1104371617⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2011138]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4030480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4030480 = ⟨1351706566, 946780243⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2015240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4112392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4112392 = ⟨1313763252, 472912507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2056196]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4153348 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4153348 = ⟨1483831035, 374604925⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2076674]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4374536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4374536 = ⟨367405970, 1192731182⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2187268]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4554768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4554768 = ⟨1160880133, 462722192⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2277384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4636680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4636680 = ⟨631465258, 970626343⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2318340]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4898824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4898824 = ⟨715871703, 1530532320⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2449412]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4915232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4915232 = ⟨1970810394, 1411035401⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2457616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5079056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5079056 = ⟨1127571674, 803918556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2539528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5160968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5160968 = ⟨1520960776, 419691142⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2580484]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5423112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5423112 = ⟨681337648, 1322381627⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2711556]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5603344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5603344 = ⟨84724475, 164917884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2801672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5636160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5636160 = ⟨957712904, 936543608⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2818080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5685256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5685256 = ⟨1830987432, 1456377183⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2842628]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5767424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5767424 = ⟨663328646, 1358879033⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2883712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5947400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5947400 = ⟨1475318213, 1772039086⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2973700]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5963808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5963808 = ⟨1449743214, 2137397420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2981904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6127632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6127632 = ⟨1682488422, 845480379⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3063816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6209544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6209544 = ⟨592622069, 576995188⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3104772]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6471688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6471688 = ⟨1617878354, 1081945519⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3235844]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6651920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6651920 = ⟨503242681, 1235758642⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3325960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6733832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6733832 = ⟨1513757503, 1831419947⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3366916]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6995976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6995976 = ⟨1818943386, 1402255777⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3497988]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7012384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7012384 = ⟨1363545803, 143407792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3506192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7078016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7078016 = ⟨243284946, 1979102606⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3539008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7176208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7176208 = ⟨1090958806, 1838962149⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3588104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7258120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7258120 = ⟨20890125, 555846051⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3629060]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7520264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7520264 = ⟨1602791012, 770382145⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3760132]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7700496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7700496 = ⟨971283854, 268607386⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3850248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7733312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7733312 = ⟨1518735151, 1912796323⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3866656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7782408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7782408 = ⟨1244125630, 1722979953⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3891204]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8044552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8044552 = ⟨705570084, 383319602⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4022276]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8060960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8060960 = ⟨1445373969, 1487439654⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4030480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8224784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8224784 = ⟨1152040327, 756140359⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4112392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8306696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8306696 = ⟨469599373, 1108944164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4153348]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8749072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8749072 = ⟨318965480, 376168196⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4374536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9109536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9109536 = ⟨2058332086, 1785946242⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4554768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9273360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9273360 = ⟨1427039207, 1293535533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4636680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9797648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9797648 = ⟨1215799418, 1769675646⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4898824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9830464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9830464 = ⟨1626800004, 2044324890⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4915232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10158112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10158112 = ⟨2086953620, 1669196392⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5079056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10321936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10321936 = ⟨1973217216, 1666722069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5160968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10846224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10846224 = ⟨731991071, 289007817⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5423112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11206688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11206688 = ⟨1834493558, 531283740⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5603344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11272320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11272320 = ⟨845391261, 2089287639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5636160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11370512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11370512 = ⟨1012315887, 1437829437⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5685256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11534848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11534848 = ⟨1319341248, 2115507030⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5767424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11894800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11894800 = ⟨1182816327, 1115165734⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5947400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11927616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11927616 = ⟨1535427605, 685217420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5963808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12255264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12255264 = ⟨87003313, 1664033203⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6127632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12419088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12419088 = ⟨147867247, 1693130445⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6209544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12943376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12943376 = ⟨1961538697, 1419830476⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6471688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13303840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13303840 = ⟨1330551075, 390818341⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6651920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13467664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13467664 = ⟨1310217316, 1463272770⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6733832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13991952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13991952 = ⟨1968485991, 1228955467⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6995976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14024768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14024768 = ⟨49499156, 1743464640⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7012384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14156032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14156032 = ⟨859704226, 1898685532⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7078016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14352416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14352416 = ⟨678576086, 317698606⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7176208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14516240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14516240 = ⟨1456315627, 597428646⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7258120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15040528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15040528 = ⟨1801879517, 470223676⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7520264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15400992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15400992 = ⟨942497488, 1735883199⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7700496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15466624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15466624 = ⟨1681864901, 229107485⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7733312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15564816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15564816 = ⟨672895583, 1435455977⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7782408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16089104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16089104 = ⟨1716088318, 1794991514⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8044552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16121920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16121920 = ⟨1924963656, 375641482⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8060960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16449568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16449568 = ⟨1088804001, 110903668⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8224784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16613392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16613392 = ⟨249904997, 1544583583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8306696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17498144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17498144 = ⟨954544317, 179928303⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8749072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18219072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18219072 = ⟨1284865097, 163770177⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9109536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18546720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18546720 = ⟨760907190, 682822808⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9273360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19595296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19595296 = ⟨1041726708, 1380408426⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9797648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19660928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19660928 = ⟨878260204, 1202482455⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9830464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20316224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20316224 = ⟨82896531, 330214504⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10158112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20643872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20643872 = ⟨1606111235, 411713340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10321936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21692448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21692448 = ⟨486485070, 1825442623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10846224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22413376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22413376 = ⟨547305780, 1400826138⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11206688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22544640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22544640 = ⟨1422905980, 1290868790⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11272320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22741024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22741024 = ⟨528249535, 1780837062⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11370512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23069696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23069696 = ⟨1952803077, 464954162⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11534848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23789600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23789600 = ⟨1082886622, 598601461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11894800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23855232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23855232 = ⟨1989080184, 1420580559⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11927616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24510528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24510528 = ⟨972474038, 316235521⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12255264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24838176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24838176 = ⟨1891139494, 63086804⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12419088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25886752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25886752 = ⟨958401997, 360561673⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12943376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26607680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26607680 = ⟨1881415718, 619246282⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13303840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26935328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26935328 = ⟨477029651, 1540525028⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13467664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27983904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27983904 = ⟨238511596, 382596562⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13991952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28049536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28049536 = ⟨692753606, 1044038572⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14024768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28312064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28312064 = ⟨117818296, 445147715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14156032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28704832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28704832 = ⟨781560198, 1063265821⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14352416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29032480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29032480 = ⟨517319100, 946084569⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14516240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30081056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30081056 = ⟨2016241989, 740792217⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15040528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30801984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30801984 = ⟨566908949, 394657329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15400992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30933248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30933248 = ⟨1746886413, 1999649059⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15466624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31129632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31129632 = ⟨1620541784, 1183907396⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15564816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32178208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32178208 = ⟨1203172065, 1814912110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16089104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32243840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32243840 = ⟨1383392430, 1055339079⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16121920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32899136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32899136 = ⟨1931017499, 1026454124⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16449568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33226784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33226784 = ⟨272710807, 1354734133⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16613392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34996288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34996288 = ⟨157753629, 31116821⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17498144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36438144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36438144 = ⟨1581645302, 239842297⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18219072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37093440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37093440 = ⟨734070488, 1365462476⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18546720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39190592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39190592 = ⟨2112363478, 1013853664⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19595296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39321856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39321856 = ⟨552758600, 1653968509⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19660928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40632448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40632448 = ⟨1996134503, 2095702053⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20316224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41287744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41287744 = ⟨2113534418, 153093092⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20643872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43384896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43384896 = ⟨1128337328, 37386135⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21692448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44826752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44826752 = ⟨1197550195, 674723081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22413376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45089280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45089280 = ⟨1402176381, 311579886⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22544640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45482048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45482048 = ⟨1282070055, 1324757498⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22741024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47579200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47579200 = ⟨1136590079, 762733696⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23789600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47710464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47710464 = ⟨1489655115, 629857263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23855232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49021056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49021056 = ⟨1284201541, 621209620⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24510528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49676352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49676352 = ⟨1125388780, 861559665⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24838176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51773504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51773504 = ⟨788141300, 1206308706⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25886752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53215360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53215360 = ⟨1643221041, 2069303916⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26607680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53870656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53870656 = ⟨792708968, 272753557⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26935328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55967808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55967808 = ⟨186683306, 755087942⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27983904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56099072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56099072 = ⟨612300750, 347846661⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28049536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56624128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56624128 = ⟨375974868, 1233265083⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28312064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57409664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57409664 = ⟨2120541682, 1121812344⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28704832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58064960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58064960 = ⟨1973329038, 582950917⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29032480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60162112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60162112 = ⟨482460718, 1449577264⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30081056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61603968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61603968 = ⟨616304131, 1316805221⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30801984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61866496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61866496 = ⟨440881565, 1840287943⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30933248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62259264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62259264 = ⟨1075545903, 44556508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31129632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64356416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64356416 = ⟨1762675037, 1411121005⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32178208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64487680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64487680 = ⟨1848192005, 825879741⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32243840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65798272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65798272 = ⟨832215309, 540865475⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32899136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66453568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66453568 = ⟨1781211883, 364705822⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33226784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69992576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69992576 = ⟨1755226639, 601873622⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34996288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72876288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72876288 = ⟨536229718, 276881210⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36438144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_74186880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 74186880 = ⟨1638355934, 208996528⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37093440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_78381184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 78381184 = ⟨1568646222, 583290313⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39190592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_78643712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 78643712 = ⟨646106130, 646630759⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39321856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_81264896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81264896 = ⟨1291639318, 182099476⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40632448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_82575488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 82575488 = ⟨2090117316, 194385367⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41287744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_86769792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86769792 = ⟨2002300155, 829266623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43384896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89653504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89653504 = ⟨1207699717, 803647142⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44826752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90178560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90178560 = ⟨324159263, 1533483219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45089280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90964096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90964096 = ⟨1109451478, 1541496191⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45482048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_95158400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 95158400 = ⟨1154230185, 98030440⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47579200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_95420928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 95420928 = ⟨146584107, 1319842497⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47710464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98042112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98042112 = ⟨1944813514, 2122862273⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49021056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_99352704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 99352704 = ⟨1922068208, 1412975792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49676352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_103547008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103547008 = ⟨1594450033, 412187907⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51773504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106430720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106430720 = ⟨1960189849, 1881673480⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53215360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_107741312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 107741312 = ⟨65511663, 1789994420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53870656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_111935616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 111935616 = ⟨808319930, 1371065056⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55967808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_112198144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112198144 = ⟨840836658, 871663464⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56099072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_114819328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114819328 = ⟨1356044803, 1788816425⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57409664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_116129920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116129920 = ⟨775172870, 1393893611⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58064960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120324224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120324224 = ⟨1951450836, 2034570490⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60162112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123207936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123207936 = ⟨1869504614, 1479869735⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61603968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123732992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123732992 = ⟨285193818, 765163688⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61866496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124518528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124518528 = ⟨1456492406, 2044567058⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62259264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_128712832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128712832 = ⟨1103481968, 1974932907⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64356416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_128975360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128975360 = ⟨401936896, 1793683774⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64487680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_131596544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131596544 = ⟨414926111, 656958002⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65798272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_132907136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 132907136 = ⟨1737066543, 1895506136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66453568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_139985152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 139985152 = ⟨1832587684, 981953392⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69992576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_145752576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 145752576 = ⟨41048732, 238473399⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72876288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_148373760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 148373760 = ⟨456938683, 1195320352⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74186880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_156762368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 156762368 = ⟨1044906908, 495027792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78381184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_157287424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 157287424 = ⟨286638124, 1789802823⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78643712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_162529792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 162529792 = ⟨651124916, 1463531762⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81264896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_165150976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 165150976 = ⟨1447367526, 1503745320⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82575488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_173539584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 173539584 = ⟨1433582165, 106586771⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86769792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_179307008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 179307008 = ⟨1632225467, 939199308⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89653504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_181928192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 181928192 = ⟨1901132422, 1082927893⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90964096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_190316800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 190316800 = ⟨1357789861, 761709439⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_95158400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_190841856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 190841856 = ⟨931200852, 642566420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_95420928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_196084224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 196084224 = ⟨54643862, 1321487679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98042112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_198705408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 198705408 = ⟨1228542763, 1748591427⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99352704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_207094016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 207094016 = ⟨565033841, 1994664881⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103547008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_212861440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 212861440 = ⟨1420808656, 1906688033⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106430720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_215482624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 215482624 = ⟨1563966374, 1866454921⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_107741312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_223871232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 223871232 = ⟨303669480, 782195973⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111935616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_224396288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 224396288 = ⟨706014569, 1757890570⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112198144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_229638656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 229638656 = ⟨558298294, 1931073923⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114819328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_232259840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 232259840 = ⟨2056387634, 1603149844⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116129920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_240648448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 240648448 = ⟨1363047892, 1065597744⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120324224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_246415872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 246415872 = ⟨569175558, 1731555329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123207936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_249037056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 249037056 = ⟨1989578841, 980109457⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124518528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_257425664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 257425664 = ⟨316509332, 1927495478⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128712832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_257950720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 257950720 = ⟨1937755996, 1620967529⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128975360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_263193088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 263193088 = ⟨1165364048, 618951992⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131596544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_265814272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 265814272 = ⟨1627375397, 2098364967⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_132907136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_279970304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 279970304 = ⟨1342950587, 1129000820⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_139985152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_291505152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 291505152 = ⟨102502428, 487991121⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_145752576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_296747520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 296747520 = ⟨385720718, 1397068674⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_148373760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_313524736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 313524736 = ⟨1815471653, 1756905214⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_156762368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_325059584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 325059584 = ⟨113762283, 452178713⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_162529792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_330301952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 330301952 = ⟨1899137015, 529879913⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_165150976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_347079168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 347079168 = ⟨1287441677, 11173896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_173539584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_358614016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 358614016 = ⟨804875961, 1759135764⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_179307008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_363856384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 363856384 = ⟨1920358247, 1078674926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_181928192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_380633600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 380633600 = ⟨1456301586, 815464918⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_190316800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_392168448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 392168448 = ⟨394346139, 1629953179⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_196084224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_397410816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 397410816 = ⟨1100972766, 798970612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_198705408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_414188032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 414188032 = ⟨363434153, 990743492⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_207094016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_425722880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 425722880 = ⟨2092563395, 1015929240⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_212861440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_430965248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 430965248 = ⟨215186955, 740241516⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_215482624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_447742464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 447742464 = ⟨1778653508, 558388913⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_223871232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_459277312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 459277312 = ⟨1681153485, 1692397259⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_229638656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_464519680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 464519680 = ⟨216715782, 1079298946⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_232259840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_481296896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 481296896 = ⟨1224296021, 1999150325⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_240648448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_492831744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 492831744 = ⟨448402140, 760266418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_246415872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_498074112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 498074112 = ⟨1729959008, 1919341010⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_249037056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_514851328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 514851328 = ⟨788793634, 1090372936⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_257425664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_526386176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 526386176 = ⟨1742951453, 411462942⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_263193088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_531628544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 531628544 = ⟨1078225498, 888397678⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_265814272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_559940608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 559940608 = ⟨464954162, 194680570⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_279970304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_593495040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 593495040 = ⟨1233265083, 1771508779⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_296747520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_627049472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 627049472 = ⟨1533483219, 1823324384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_313524736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_660603904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 660603904 = ⟨765163688, 1862289829⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_330301952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_694158336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 694158336 = ⟨1789802823, 1860845523⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_347079168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_727712768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 727712768 = ⟨642566420, 1216282795⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_363856384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_761267200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 761267200 = ⟨1757890570, 1441469078⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_380633600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_794821632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 794821632 = ⟨1620967529, 209727651⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_397410816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_828376064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 828376064 = ⟨487991121, 2044981219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_414188032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_861930496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 861930496 = ⟨452178713, 2033721364⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_430965248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_895484928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 895484928 = ⟨1759135764, 1342607686⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_447742464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_929039360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 929039360 = ⟨1629953179, 1753137508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_464519680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_962593792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 962593792 = ⟨1015929240, 54920252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_481296896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_996148224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 996148224 = ⟨1692397259, 466330162⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_498074112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1029702656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1029702656 = ⟨760266418, 1699081507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_514851328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1063257088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1063257088 = ⟨411462942, 404532194⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_531628544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 416) = ⟨1952803077, 464954162⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 416 = 23069696 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_23069696

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1952803077, 464954162⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 416) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 417) = ⟨464954162, 194680570⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 417 = 559940608 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_559940608

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨464954162, 194680570⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 417) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 418) = ⟨102502428, 487991121⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 418 = 291505152 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_291505152

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨102502428, 487991121⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 418) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 419) = ⟨487991121, 2044981219⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 419 = 828376064 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_828376064

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨487991121, 2044981219⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 419) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 420) = ⟨286638124, 1789802823⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 420 = 157287424 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_157287424

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨286638124, 1789802823⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 420) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 421) = ⟨1789802823, 1860845523⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 421 = 694158336 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_694158336

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1789802823, 1860845523⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 421) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 422) = ⟨2092563395, 1015929240⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 422 = 425722880 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_425722880

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2092563395, 1015929240⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 422) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 423) = ⟨1015929240, 54920252⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 423 = 962593792 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_962593792

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1015929240, 54920252⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 423) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 424) = ⟨324159263, 1533483219⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 424 = 90178560 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_90178560

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨324159263, 1533483219⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 424) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 425) = ⟨1533483219, 1823324384⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 425 = 627049472 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_627049472

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1533483219, 1823324384⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 425) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 426) = ⟨804875961, 1759135764⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 426 = 358614016 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_358614016

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨804875961, 1759135764⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 426) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 427) = ⟨1759135764, 1342607686⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 427 = 895484928 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_895484928

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1759135764, 1342607686⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 427) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 428) = ⟨706014569, 1757890570⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 428 = 224396288 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_224396288

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨706014569, 1757890570⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 428) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 429) = ⟨1757890570, 1441469078⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 429 = 761267200 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_761267200

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1757890570, 1441469078⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 429) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 430) = ⟨448402140, 760266418⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 430 = 492831744 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_492831744

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨448402140, 760266418⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 430) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 431) = ⟨760266418, 1699081507⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 431 = 1029702656 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1029702656

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨760266418, 1699081507⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 431) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 432) = ⟨375974868, 1233265083⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 432 = 56624128 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_56624128

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨375974868, 1233265083⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 432) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 433) = ⟨1233265083, 1771508779⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 433 = 593495040 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_593495040

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1233265083, 1771508779⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 433) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 434) = ⟨113762283, 452178713⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 434 = 325059584 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_325059584

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨113762283, 452178713⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 434) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 435) = ⟨452178713, 2033721364⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 435 = 861930496 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_861930496

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨452178713, 2033721364⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 435) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 436) = ⟨931200852, 642566420⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 436 = 190841856 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_190841856

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨931200852, 642566420⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 436) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 437) = ⟨642566420, 1216282795⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 437 = 727712768 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_727712768

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨642566420, 1216282795⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 437) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 438) = ⟨1681153485, 1692397259⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 438 = 459277312 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_459277312

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1681153485, 1692397259⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 438) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 439) = ⟨1692397259, 466330162⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 439 = 996148224 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_996148224

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1692397259, 466330162⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 439) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 440) = ⟨285193818, 765163688⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 440 = 123732992 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_123732992

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨285193818, 765163688⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 440) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 441) = ⟨765163688, 1862289829⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 441 = 660603904 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_660603904

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨765163688, 1862289829⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 441) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 442) = ⟨394346139, 1629953179⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 442 = 392168448 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_392168448

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨394346139, 1629953179⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 442) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 443) = ⟨1629953179, 1753137508⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 443 = 929039360 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_929039360

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1629953179, 1753137508⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 443) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 444) = ⟨1937755996, 1620967529⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 444 = 257950720 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_257950720

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1937755996, 1620967529⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 444) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 445) = ⟨1620967529, 209727651⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 445 = 794821632 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_794821632

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1620967529, 209727651⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 445) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 446) = ⟨1742951453, 411462942⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 446 = 526386176 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_526386176

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1742951453, 411462942⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 446) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 447) = ⟨411462942, 404532194⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 447 = 1063257088 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1063257088

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨411462942, 404532194⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 447) := by
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

end R17TableAChunk13Certificate
