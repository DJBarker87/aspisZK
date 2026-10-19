import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk09Certificate
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

theorem power_36 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36 = ⟨1215140682, 1809443407⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18]
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

theorem power_60 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60 = ⟨1978400158, 1658303135⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30]
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

theorem power_68 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 68 = ⟨1252169843, 628159355⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_70 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70 = ⟨115184242, 829081638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72 = ⟨360409545, 241565342⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73 = ⟨1859610645, 698599623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_74 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 74 = ⟨635582094, 405349503⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76 = ⟨2095288830, 1138360406⟩ := by
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

theorem power_84 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84 = ⟨1543107831, 276086046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_86 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86 = ⟨1687815885, 1893568127⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89 = ⟨797347039, 1803718760⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90 = ⟨430426420, 308360131⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92 = ⟨1119524497, 1705494219⟩ := by
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

theorem power_100 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100 = ⟨1307625421, 302110264⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102 = ⟨1516486685, 2082671253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105 = ⟨244648141, 849348041⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106 = ⟨382757218, 311908650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108 = ⟨467798412, 1281237586⟩ := by
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

theorem power_118 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118 = ⟨2029146254, 280154270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121 = ⟨663578559, 2077989577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122 = ⟨910427772, 437706403⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124 = ⟨264684109, 401121384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126 = ⟨647666107, 883025679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_132 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 132 = ⟨198245992, 796735524⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_137 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 137 = ⟨1581084279, 1857932412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_140 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 140 = ⟨166789141, 776909418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 144 = ⟨552528648, 1672522617⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_146 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 146 = ⟨1394961978, 1918912426⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_148 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 148 = ⟨1797069868, 1569931230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_153 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 153 = ⟨1201477885, 724709579⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_156 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 156 = ⟨58128200, 444904138⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_164 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 164 = ⟨1808739933, 169886250⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_169 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 169 = ⟨2036465601, 1803091641⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_172 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 172 = ⟨1271351363, 2142894890⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_178 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 178 = ⟨1966870087, 1210006847⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_180 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 180 = ⟨440283696, 1083008219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_185 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 185 = ⟨1288520283, 160642759⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_188 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 188 = ⟨528927296, 843766190⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94]
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

theorem power_201 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 201 = ⟨1520147888, 325985670⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_204 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 204 = ⟨349974108, 1382066042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_210 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 210 = ⟨1496414007, 1479063729⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_212 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 212 = ⟨224723496, 98912589⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_217 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 217 = ⟨2139901027, 71265922⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_220 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 220 = ⟨103472470, 1652631780⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_228 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 228 = ⟨470360473, 1771595164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_233 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 233 = ⟨145382460, 620920719⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_236 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 236 = ⟨1882349838, 1929949081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_242 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 242 = ⟨1632899039, 338964697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_244 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 244 = ⟨840379230, 2035177650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_249 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 249 = ⟨1744129065, 1490136674⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_252 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 252 = ⟨1105406260, 2088944411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_265 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 265 = ⟨663717594, 300942251⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_132]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_274 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 274 = ⟨2072356374, 911719338⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_137]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_281 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 281 = ⟨40358786, 1014147237⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_140]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 288 = ⟨1178716014, 1579375203⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_292 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 292 = ⟨1014560274, 418534048⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_146]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_297 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 297 = ⟨1089920815, 970667017⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_148]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_306 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 306 = ⟨1302783265, 1840133980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_153]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_313 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 313 = ⟨692409925, 614581547⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_156]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 328 = ⟨926055753, 540139726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_164]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_329 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 329 = ⟨1967088239, 856881324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_164]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_338 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 338 = ⟨1774142499, 1307308901⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_169]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_345 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 345 = ⟨1881883597, 1693089677⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_172]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_356 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 356 = ⟨115833841, 1001104970⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_178]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_361 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 361 = ⟨669084783, 186474006⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_180]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_370 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 370 = ⟨437004439, 622531583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_185]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_377 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 377 = ⟨612034136, 2076531586⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_188]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_393 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 393 = ⟨1548598224, 1016018293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_196]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 400 = ⟨1872990432, 1178172302⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_402 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 402 = ⟨684316640, 356521895⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_201]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_409 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 409 = ⟨615691347, 1695517224⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_204]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_420 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 420 = ⟨762451310, 2110959177⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_210]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_425 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 425 = ⟨763714137, 1274194053⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_212]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_434 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 434 = ⟨945282890, 1431558057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_217]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_441 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 441 = ⟨1650661418, 42675051⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_220]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 456 = ⟨1050515860, 1972726217⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_228]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_457 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 457 = ⟨618581785, 1299048615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_228]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_466 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 466 = ⟨1124251816, 63530739⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_233]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_473 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 473 = ⟨1754927637, 1983922795⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_236]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_484 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 484 = ⟨1722484487, 1875389337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_242]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_489 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 489 = ⟨561470423, 1602268084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_244]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_498 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 498 = ⟨1596061297, 646835308⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_249]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_505 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 505 = ⟨1317526403, 250807280⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_252]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_530 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 530 = ⟨1302204800, 247316364⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_265]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_548 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 548 = ⟨866115909, 1643827515⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_274]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_562 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 562 = ⟨1389248942, 830401317⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_281]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 576 = ⟨1603309155, 1317339952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 584 = ⟨1408296071, 1181839931⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_292]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_594 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 594 = ⟨599739366, 1596664233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_297]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_612 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 612 = ⟨2046256912, 509115615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_306]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_626 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 626 = ⟨187039448, 377126727⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_313]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 656 = ⟨1195617483, 37201067⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_658 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 658 = ⟨1942116078, 1259378941⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_329]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_676 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 676 = ⟨393415872, 860368912⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_338]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_690 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 690 = ⟨909995743, 1217441152⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_345]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 712 = ⟨1788714561, 1660296709⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_356]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_722 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 722 = ⟨1324451431, 141767293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_361]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_740 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 740 = ⟨197719403, 1999852429⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_370]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_754 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 754 = ⟨1259318179, 1183920775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_377]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_786 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 786 = ⟨250801248, 948516604⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_393]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 800 = ⟨1630963856, 82519081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_804 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 804 = ⟨26399338, 967637504⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_402]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_818 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 818 = ⟨1240245163, 2079245213⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_409]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 840 = ⟨667660294, 1845636271⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_420]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_850 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 850 = ⟨890897098, 2137886324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_425]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_868 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 868 = ⟨2142650926, 908959764⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_434]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_882 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 882 = ⟨1288167735, 1920555476⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_441]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 912 = ⟨345462981, 482925972⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_914 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 914 = ⟨1393070476, 66381129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_457]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_932 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 932 = ⟨1976405820, 1310158830⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_466]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_946 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 946 = ⟨1342970141, 165874054⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_473]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 968 = ⟨331985874, 1829534965⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_484]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_978 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 978 = ⟨1932071536, 528143660⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_489]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_996 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 996 = ⟨908566887, 550594540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_498]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1010 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1010 = ⟨153293190, 250253391⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_505]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1060 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1060 = ⟨344350850, 736155373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_530]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1096 = ⟨1501894557, 1834033800⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_548]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1124 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1124 = ⟨1692845452, 528912612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_562]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1152 = ⟨2144756169, 1973977555⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1168 = ⟨341432789, 740546388⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1188 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1188 = ⟨190880788, 1632498209⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_594]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1224 = ⟨1026227221, 2108794965⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_612]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1252 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1252 = ⟨1915998887, 1807225347⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_626]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1312 = ⟨1361133795, 1467941404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1316 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1316 = ⟨903495951, 1860187544⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_658]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1352 = ⟨1927061498, 1374927155⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_676]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1380 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1380 = ⟨1653387921, 765984511⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_690]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1424 = ⟨1421359463, 688309433⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1444 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1444 = ⟨308036086, 726910375⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_722]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1480 = ⟨722960591, 588699063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_740]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1508 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1508 = ⟨2086867373, 788275304⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_754]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1572 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1572 = ⟨50342264, 1978562733⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_786]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1600 = ⟨517742188, 968413651⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1608 = ⟨62787373, 919735329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_804]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1636 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1636 = ⟨960080072, 1622267454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_818]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1680 = ⟨97994513, 427567333⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1700 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1700 = ⟨372157944, 812196632⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_850]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1736 = ⟨467721784, 1602005661⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_868]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1764 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1764 = ⟨2137299651, 284745709⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_882]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1824 = ⟨1157368979, 1934990557⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1828 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1828 = ⟨1387922376, 1867094734⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_914]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1864 = ⟨1968067598, 686949896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_932]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1892 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1892 = ⟨1585159075, 1178205878⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_946]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1936 = ⟨440725243, 397214378⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1956 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1956 = ⟨1637848734, 1513201997⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_978]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1992 = ⟨1008494537, 585464310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_996]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2020 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2020 = ⟨1895568491, 1249163611⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1010]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2120 = ⟨2139658876, 1203399882⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1060]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2192 = ⟨1742105348, 871429063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2248 = ⟨2132144787, 1100042412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1124]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2304 = ⟨505774551, 1187398701⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2336 = ⟨1969372346, 488760614⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2376 = ⟨1314294427, 861033725⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1188]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2448 = ⟨481345752, 412268047⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2504 = ⟨2072615499, 555582780⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1252]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2624 = ⟨1221120023, 1584263814⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2632 = ⟨1434034637, 1839808670⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1316]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2704 = ⟨1366684352, 516929062⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2760 = ⟨906757229, 1075779125⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1380]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2848 = ⟨1107539930, 1867229522⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2888 = ⟨685906655, 1741991838⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1444]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2960 = ⟨2097605752, 220649565⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3016 = ⟨2077055915, 684906070⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1508]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3144 = ⟨764630114, 96470594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1572]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3200 = ⟨1230785717, 932947748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3216 = ⟨731685287, 762627775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3272 = ⟨64561430, 1495376147⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1636]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3360 = ⟨957961597, 1713758465⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3400 = ⟨1046641189, 847897017⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1700]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3472 = ⟨1911499284, 1489701003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3528 = ⟨2103592301, 25088337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1764]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3648 = ⟨2120725548, 846203964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3656 = ⟨676028118, 399800502⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1828]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3728 = ⟨390407353, 375027877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3784 = ⟨1308466044, 2061209628⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1892]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3872 = ⟨732405916, 440343212⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3912 = ⟨1856790920, 1065580309⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1956]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3984 = ⟨1686898389, 320083871⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4040 = ⟨1879568841, 153268685⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2020]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4240 = ⟨269885647, 1493923036⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4384 = ⟨1196533489, 306824470⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4496 = ⟨340501265, 1876078032⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4608 = ⟨1781794005, 336873408⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4672 = ⟨2028679962, 456227245⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4752 = ⟨507665041, 1847684026⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4896 = ⟨23461219, 810403446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5008 = ⟨352236765, 1841049662⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5248 = ⟨1290866284, 1587498888⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5264 = ⟨1782774083, 405367834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5408 = ⟨2064549844, 501529631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5520 = ⟨2050717322, 977851938⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5696 = ⟨979531440, 1806178696⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5776 = ⟨1664736485, 1300352427⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5920 = ⟨878312693, 56859138⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6032 = ⟨1960702907, 650095777⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6288 = ⟨288189657, 1392794513⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6400 = ⟨977208331, 1995798003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6432 = ⟨619638383, 840515631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6544 = ⟨1063294853, 115379435⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6720 = ⟨618506335, 666669213⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6800 = ⟨302380768, 635890107⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6944 = ⟨1264135541, 1176714595⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7056 = ⟨1312052969, 29746588⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7296 = ⟨236244120, 866051848⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7312 = ⟨1114260757, 159667207⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7456 = ⟨645077113, 2009296946⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7568 = ⟨1914237748, 709133042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7744 = ⟨1314764028, 76457491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7824 = ⟨1731399696, 435779351⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7968 = ⟨1615077929, 1550574971⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8080 = ⟨1053814494, 1416824671⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8480 = ⟨328984271, 166699669⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8768 = ⟨1312321620, 449496866⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8992 = ⟨1041821071, 514323391⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9216 = ⟨1702571195, 1397706324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9344 = ⟨1549016389, 59136170⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9504 = ⟨736822772, 429173123⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9792 = ⟨1641904899, 479652953⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10016 = ⟨1670001736, 701104923⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10496 = ⟨1825573200, 854560364⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10528 = ⟨451735254, 662637945⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10816 = ⟨589196420, 1478404190⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11040 = ⟨779218934, 116077555⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11392 = ⟨1624277146, 218264369⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11552 = ⟨251658599, 336116018⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11840 = ⟨1936539270, 2080532700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12064 = ⟨926722675, 981181323⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12576 = ⟨230679026, 1944561765⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12800 = ⟨670508625, 2057653994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12864 = ⟨1849520254, 294275432⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13088 = ⟨631181895, 1822364160⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13440 = ⟨1254228892, 1773606283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13600 = ⟨716825451, 356967739⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13888 = ⟨999173566, 53735745⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14112 = ⟨803372743, 168519937⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14592 = ⟨2040419523, 293774007⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14624 = ⟨2096924257, 548262718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14912 = ⟨1832078956, 1219025627⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15136 = ⟨1828745539, 489103839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15488 = ⟨2114691705, 1438921723⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15648 = ⟨892110449, 220067801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15936 = ⟨1702528037, 2011195799⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16160 = ⟨561025894, 465124133⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16960 = ⟨394740625, 723911021⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17536 = ⟨1806498481, 2062496117⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17984 = ⟨314868156, 243309129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18433 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18433 = ⟨1338646949, 1494232902⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18688 = ⟨645114853, 992481545⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19008 = ⟨1784287278, 1544688091⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19584 = ⟨1580867433, 1644740200⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20032 = ⟨1265329328, 251621816⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20992 = ⟨2108569002, 332819919⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21056 = ⟨1847141625, 1093490603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21632 = ⟨2099551557, 403675340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22080 = ⟨1642534031, 747827091⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22784 = ⟨136897115, 493987288⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23104 = ⟨663220105, 287929876⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23680 = ⟨854568819, 1347442685⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24128 = ⟨846618056, 1441479448⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25152 = ⟨134399133, 2040035251⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25600 = ⟨1627995231, 271303573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25728 = ⟨1759013300, 1042401069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26176 = ⟨220043234, 983428254⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26880 = ⟨676135582, 533441857⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27200 = ⟨1239413719, 1027904586⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27776 = ⟨1834226232, 553776749⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28224 = ⟨1948043557, 610412763⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29184 = ⟨212160839, 1626753054⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29248 = ⟨253349534, 1858123601⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29824 = ⟨1483663201, 1628565788⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30272 = ⟨970846431, 1711895041⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30976 = ⟨1799654460, 431926545⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31296 = ⟨991091046, 191490810⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31872 = ⟨1943795279, 465690519⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32320 = ⟨1169520461, 711190012⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33920 = ⟨1311557298, 1822393781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35072 = ⟨1205114505, 1030165210⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35968 = ⟨952035444, 1885921242⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36866 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36866 = ⟨1226402341, 948846718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18433]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37376 = ⟨1433248480, 2047948056⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38016 = ⟨594961630, 1538607351⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39168 = ⟨1100489519, 1086275843⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40064 = ⟨1045715505, 563126510⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41984 = ⟨2071856540, 882531073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42112 = ⟨827878747, 241314994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43264 = ⟨1891533946, 2050936908⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44160 = ⟨154470508, 1192247807⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45568 = ⟨1781787493, 1860062069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46208 = ⟨430504778, 1955295500⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47360 = ⟨578477849, 1590460480⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48256 = ⟨356492786, 1180332870⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50304 = ⟨1944732118, 978402005⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51201 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51201 = ⟨284012004, 1744646782⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51456 = ⟨1116504179, 647757200⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52352 = ⟨1901124201, 2143771058⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53760 = ⟨2139509494, 188640990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54400 = ⟨49131791, 1851403731⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55552 = ⟨114992383, 2037241690⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56448 = ⟨518956235, 1383201958⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58368 = ⟨287812835, 2081660990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58496 = ⟨248346185, 1121744840⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59648 = ⟨724181499, 1793728645⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60544 = ⟨1470372661, 506642412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61952 = ⟨489478772, 1893340241⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62592 = ⟨1416818600, 2054427749⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63744 = ⟨1980320235, 603453234⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64640 = ⟨618833431, 476874519⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_67840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67840 = ⟨508357421, 395335057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_70144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70144 = ⟨595073736, 1818489881⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71936 = ⟨1893022049, 594192⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73732 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73732 = ⟨1442273005, 1539027801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36866]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_74752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 74752 = ⟨650673267, 783237242⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76032 = ⟨1148369502, 804278035⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_78336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 78336 = ⟨411448928, 233625844⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_80128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 80128 = ⟨1418778797, 258296867⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_83969 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83969 = ⟨1013207202, 1946460779⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_84224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84224 = ⟨211361362, 1028809813⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_86528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86528 = ⟨434707223, 1389804667⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88320 = ⟨726724975, 1168558912⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_91136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 91136 = ⟨1033720207, 1183348280⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92416 = ⟨31335748, 918885051⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94720 = ⟨655661521, 997404908⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_96512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96512 = ⟨543798714, 1802097055⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_100608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100608 = ⟨842920915, 347205840⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102402 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102402 = ⟨1627795390, 1242413369⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51201]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102912 = ⟨1504273585, 1801154452⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104704 = ⟨613410698, 1808278436⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_107520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 107520 = ⟨250559477, 97699828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108800 = ⟨412732311, 1269419365⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_111104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 111104 = ⟨1107514854, 789018799⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_112896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112896 = ⟨1577363018, 553400799⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_116737 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116737 = ⟨1407696362, 1469886383⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_116992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116992 = ⟨1250900219, 636456966⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_119296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119296 = ⟨383390103, 624803601⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121088 = ⟨1100759221, 758754175⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123904 = ⟨1105219207, 965100990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125184 = ⟨325369858, 167222949⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_127488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 127488 = ⟨829291870, 806666746⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_129280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 129280 = ⟨1576913313, 1739575071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_135680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 135680 = ⟨467649725, 454444306⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_140288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 140288 = ⟨809678638, 323259731⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_143872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 143872 = ⟨393854136, 1965558320⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_147464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 147464 = ⟨1831659930, 553627133⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73732]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_149505 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 149505 = ⟨1475558691, 222082686⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_152064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 152064 = ⟨805179065, 529723806⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_156672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 156672 = ⟨2038368826, 1106226198⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_160256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 160256 = ⟨1942375017, 1931199302⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_167938 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 167938 = ⟨1223164275, 879927578⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83969]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_168448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 168448 = ⟨1706131002, 167271241⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_173056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 173056 = ⟨737486420, 1841785488⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_176640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 176640 = ⟨1131775757, 678881614⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_182273 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 182273 = ⟨1019897140, 1659123360⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_184832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 184832 = ⟨1590126683, 67711264⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_189440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 189440 = ⟨1040456537, 1941786120⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_193024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 193024 = ⟨932412059, 587449463⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_201216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 201216 = ⟨889292995, 2145182579⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_204804 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 204804 = ⟨380986201, 1196544990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102402]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_205824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 205824 = ⟨1412850982, 862664749⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_209408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 209408 = ⟨806343892, 316887547⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_215041 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 215041 = ⟨1077742981, 779972869⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_107520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_217600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 217600 = ⟨574779494, 501086924⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_222208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 222208 = ⟨881063582, 942487649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_225792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 225792 = ⟨1992672151, 1883997027⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_233474 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 233474 = ⟨2019495807, 8913737⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116737]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_233984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 233984 = ⟨2030960760, 1034743639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_238592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 238592 = ⟨1558946112, 74958411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_242176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 242176 = ⟨1898504412, 2020670990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_247809 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 247809 = ⟨1990430319, 1512104551⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_250368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 250368 = ⟨1090941090, 130231932⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_254976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 254976 = ⟨399181318, 1588403662⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_127488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_258560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 258560 = ⟨1276767966, 2146293151⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_129280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_271360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 271360 = ⟨2031338353, 1171105428⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_135680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_280577 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 280577 = ⟨1081863138, 1568435911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_140288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_287744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 287744 = ⟨179957683, 618553811⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_143872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_294928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 294928 = ⟨1181777025, 395737841⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_147464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_299010 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 299010 = ⟨1257525309, 922143153⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_149505]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_304128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 304128 = ⟨1877383557, 1174650430⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_152064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_313345 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 313345 = ⟨368747376, 593735023⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_156672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_320512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 320512 = ⟨1569243112, 1043148296⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_160256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_335876 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 335876 = ⟨1945206686, 1595803473⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_167938]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_336896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 336896 = ⟨1048079598, 1664012201⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_168448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_346113 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 346113 = ⟨1794052989, 1418896067⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_173056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_353280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 353280 = ⟨1432115175, 1175896303⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_176640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_364546 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 364546 = ⟨904012528, 1379868899⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_182273]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_369664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 369664 = ⟨73683083, 1009582096⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_184832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_378881 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 378881 = ⟨356307157, 981808004⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_189440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_386048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 386048 = ⟨1974927939, 1591951531⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_193024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_402432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 402432 = ⟨1561465757, 1257811516⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_201216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_409608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 409608 = ⟨1692311620, 972900177⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_204804]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_411649 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 411649 = ⟨654158008, 641468172⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_205824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_418816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 418816 = ⟨1739022919, 299936075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_209408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_430082 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 430082 = ⟨615244665, 383630233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_215041]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_435200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 435200 = ⟨238661036, 428034347⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_217600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_444417 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 444417 = ⟨275617562, 204538147⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_222208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_451584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 451584 = ⟨2081843833, 1308756649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_225792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_466948 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 466948 = ⟨80300369, 1485021340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_233474]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_467968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 467968 = ⟨1597597014, 843895897⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_233984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_477185 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 477185 = ⟨226942059, 835123983⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_238592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_484352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 484352 = ⟨1285025349, 1411487338⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_242176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_495618 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 495618 = ⟨1696556918, 233541399⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_247809]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_500736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 500736 = ⟨1012753014, 1231443995⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_250368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_509953 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 509953 = ⟨505193733, 485235031⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_254976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_517120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 517120 = ⟨116962009, 1390307281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_258560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_542721 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 542721 = ⟨1113485063, 1635083324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_271360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_561154 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 561154 = ⟨1241657021, 1417700311⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_280577]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_575489 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 575489 = ⟨1963905657, 1885891457⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_287744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_589856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 589856 = ⟨1080117264, 93809300⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_294928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_598020 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 598020 = ⟨2057632578, 2104617304⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_299010]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_608257 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 608257 = ⟨1958871429, 554104228⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_304128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_626690 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 626690 = ⟨96203471, 1694918597⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_313345]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_641025 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 641025 = ⟨1003711123, 72328909⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_320512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_671752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 671752 = ⟨1212136686, 1831224800⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_335876]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_673793 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 673793 = ⟨1416318573, 197070834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_336896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_692226 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 692226 = ⟨74384310, 1287958362⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_346113]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_706561 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 706561 = ⟨1628748394, 631741220⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_353280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_729092 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 729092 = ⟨1449585379, 1327814830⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_364546]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_739329 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 739329 = ⟨1483282097, 39576471⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_369664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_757762 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 757762 = ⟨124896583, 917080675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_378881]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_772097 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 772097 = ⟨1484896006, 1584182493⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_386048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_804865 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 804865 = ⟨1017008157, 645472948⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_402432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_819216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 819216 = ⟨327475038, 999594557⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_409608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_823298 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 823298 = ⟨763702837, 1418530694⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_411649]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_837633 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 837633 = ⟨1433140127, 1508299613⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_418816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_860164 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 860164 = ⟨9358320, 197971935⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_430082]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_870401 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 870401 = ⟨856809485, 341578556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_435200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_888834 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 888834 = ⟨249488508, 607823267⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_444417]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_903169 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 903169 = ⟨383115929, 1054647923⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_451584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_933896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 933896 = ⟨2092841339, 813381516⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_466948]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_935937 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 935937 = ⟨1434164702, 1294745576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_467968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_954370 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 954370 = ⟨980684586, 1111446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_477185]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_968705 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 968705 = ⟨359130540, 881898165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_484352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_991236 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 991236 = ⟨1217364669, 1172110750⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_495618]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1001473 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1001473 = ⟨793916371, 1480355588⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_500736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1019906 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1019906 = ⟨1830407095, 1988542756⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_509953]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1034241 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1034241 = ⟨564182936, 887033899⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_517120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1085442 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1085442 = ⟨1869182134, 309878820⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_542721]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1122308 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1122308 = ⟨1687026489, 646448288⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_561154]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1150978 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1150978 = ⟨1856483163, 214577406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_575489]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1179712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1179712 = ⟨563422718, 682130653⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_589856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1196040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1196040 = ⟨22782272, 1467180691⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_598020]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1216514 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1216514 = ⟨3026894, 133644163⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_608257]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1253380 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1253380 = ⟨1844415651, 1365734063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_626690]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1282050 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1282050 = ⟨1900849075, 1636892410⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_641025]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1343504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1343504 = ⟨582255385, 155365120⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_671752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1347586 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1347586 = ⟨1302566554, 573932245⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_673793]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1384452 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1384452 = ⟨1343368142, 690152577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_692226]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1413122 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1413122 = ⟨199181200, 2063270656⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_706561]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1458184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1458184 = ⟨91539284, 888612079⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_729092]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1478658 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1478658 = ⟨411793335, 323937109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_739329]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1515524 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1515524 = ⟨1179017415, 1556666339⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_757762]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1544194 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1544194 = ⟨674293376, 284903985⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_772097]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1609730 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1609730 = ⟨1663476835, 1203968135⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_804865]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1638432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1638432 = ⟨631096707, 1424710405⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_819216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1646596 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1646596 = ⟨2066910223, 760985238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_823298]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1675266 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1675266 = ⟨981066769, 955198364⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_837633]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1720328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1720328 = ⟨1097744538, 221233191⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_860164]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1740802 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1740802 = ⟨274858852, 960103207⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_870401]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1777668 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1777668 = ⟨1231995993, 855232233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_888834]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1806338 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1806338 = ⟨1451152757, 258863001⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_903169]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1867792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1867792 = ⟨35346005, 1735560575⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_933896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1871874 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1871874 = ⟨1938383649, 2133146279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_935937]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1908740 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1908740 = ⟨1129255866, 173516425⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_954370]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1937410 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1937410 = ⟨873672322, 325240158⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_968705]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1982472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1982472 = ⟨370747144, 530331932⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_991236]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2002946 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2002946 = ⟨307275140, 1604865792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1001473]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2039812 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2039812 = ⟨1034904047, 1443659860⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1019906]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2068482 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2068482 = ⟨208907732, 176893270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1034241]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2170884 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2170884 = ⟨1324703075, 267946267⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1085442]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2244616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2244616 = ⟨346198383, 913166692⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1122308]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2301956 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2301956 = ⟨687945428, 1346051947⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1150978]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2359424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2359424 = ⟨138279626, 1258768723⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1179712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2392080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2392080 = ⟨304775225, 1964323205⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1196040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2433028 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2433028 = ⟨1844098267, 1851134076⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1216514]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2506760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2506760 = ⟨605083453, 63066975⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1253380]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2564100 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2564100 = ⟨1423514194, 1654102948⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1282050]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2687008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2687008 = ⟨392624462, 723892604⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1343504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2695172 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2695172 = ⟨1738075598, 1148245621⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1347586]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2768904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2768904 = ⟨1159407155, 1652973877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1384452]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2826244 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2826244 = ⟨1335700499, 247826678⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1413122]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2916368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2916368 = ⟨253655897, 1354220195⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1458184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2957316 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2957316 = ⟨450171735, 1205318201⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1478658]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3031048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3031048 = ⟨402519673, 2083493636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1515524]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3088388 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3088388 = ⟨408012156, 832849151⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1544194]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3219460 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3219460 = ⟨729915513, 429067909⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1609730]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3276864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3276864 = ⟨138261344, 1795178794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1638432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3293192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3293192 = ⟨1176454152, 1851493222⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1646596]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3350532 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3350532 = ⟨1676568517, 854513999⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1675266]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3440656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3440656 = ⟨1412393582, 981853557⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1720328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3481604 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3481604 = ⟨896046571, 1776780574⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1740802]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3555336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3555336 = ⟨2120891777, 1665126339⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1777668]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3612676 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3612676 = ⟨1328916471, 1185409461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1806338]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3735584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3735584 = ⟨1311256963, 22351521⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1867792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3743748 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3743748 = ⟨469497774, 1228676884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1871874]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3817480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3817480 = ⟨1533819209, 327474893⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1908740]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3874820 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3874820 = ⟨702358874, 989350717⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1937410]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3964944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3964944 = ⟨313013559, 361511343⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1982472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4005892 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4005892 = ⟨1615108824, 382162942⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2002946]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4079624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4079624 = ⟨468069773, 1918827779⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2039812]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4136964 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4136964 = ⟨124559717, 1595570600⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2068482]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4341768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4341768 = ⟨1283975394, 1664731829⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2170884]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4489232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4489232 = ⟨2094863383, 1317760976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2244616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4603912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4603912 = ⟨1561447780, 191533825⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2301956]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4718848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4718848 = ⟨888539519, 1307403545⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2359424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4784160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4784160 = ⟨855776698, 1775551394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2392080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4866056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4866056 = ⟨2030582648, 1184746164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2433028]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5013520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5013520 = ⟨495058852, 1487116644⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2506760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5128200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5128200 = ⟨1408125461, 1937404911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2564100]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5374016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5374016 = ⟨1248874597, 1416051307⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2687008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5390344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5390344 = ⟨851431012, 1382476220⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2695172]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5537808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5537808 = ⟨1871245875, 603399019⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2768904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5652488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5652488 = ⟨80910749, 2088960083⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2826244]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5832736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5832736 = ⟨673686071, 1276585⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2916368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5914632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5914632 = ⟨1136129084, 503867576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2957316]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6062096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6062096 = ⟨904659788, 1068390000⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3031048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6176776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6176776 = ⟨719185078, 1972261884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3088388]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6438920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6438920 = ⟨648423568, 1620481028⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3219460]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6553728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6553728 = ⟨1945006162, 1461504968⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3276864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6586384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6586384 = ⟨618460311, 191164543⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3293192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6701064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6701064 = ⟨281101392, 249772170⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3350532]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6881312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6881312 = ⟨1342384393, 50802013⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3440656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6963208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6963208 = ⟨369667751, 1556355997⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3481604]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7110672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7110672 = ⟨1827174538, 886616736⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3555336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7225352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7225352 = ⟨989660231, 1028891198⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3612676]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7471168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7471168 = ⟨209249279, 479664843⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3735584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7487496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7487496 = ⟨837217664, 1525712769⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3743748]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7634960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7634960 = ⟨325822347, 601377126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3817480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7749640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7749640 = ⟨1225825096, 1413045477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3874820]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7929888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7929888 = ⟨1139800999, 706433389⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3964944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8011784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8011784 = ⟨1369392786, 662012807⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4005892]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8159248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8159248 = ⟨1259811223, 1456811215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4079624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8273928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8273928 = ⟨852287329, 951165024⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4136964]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8683536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8683536 = ⟨535869630, 721375043⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4341768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8978464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8978464 = ⟨1714347434, 216273450⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4489232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9207824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9207824 = ⟨796549118, 1802403159⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4603912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9437696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9437696 = ⟨1555028808, 925796095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4718848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9568320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9568320 = ⟨1432270265, 1818232603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4784160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9732112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9732112 = ⟨1334063725, 1210607956⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4866056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10027040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10027040 = ⟨582687194, 1691872625⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5013520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10256400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10256400 = ⟨1393152719, 1592915099⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5128200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10748032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10748032 = ⟨30609077, 2042786470⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5374016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10780688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10780688 = ⟨125312882, 2020640344⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5390344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11075616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11075616 = ⟨755571068, 1036779350⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5537808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11304976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11304976 = ⟨333388998, 2023720070⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5652488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11665472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11665472 = ⟨541651697, 1596379479⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5832736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11829264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11829264 = ⟨1161565241, 1114044040⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5914632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12124192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12124192 = ⟨1170475245, 1504782395⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6062096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12353552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12353552 = ⟨1775738952, 734872833⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6176776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12877840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12877840 = ⟨1504813452, 388755498⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6438920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13107456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13107456 = ⟨1031803011, 913167940⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6553728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13172768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13172768 = ⟨531361824, 1952312223⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6586384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13402128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13402128 = ⟨706223047, 134637949⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6701064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13762624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13762624 = ⟨496741216, 922753413⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6881312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13926416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13926416 = ⟨851761953, 1931833854⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6963208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14221344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14221344 = ⟨2132228100, 1023686398⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7110672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14450704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14450704 = ⟨1999574887, 545795107⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7225352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14942336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14942336 = ⟨1722460634, 443398300⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7471168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14974992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14974992 = ⟨1670733033, 1881187486⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7487496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15269920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15269920 = ⟨1100344193, 650594815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7634960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15499280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15499280 = ⟨30043915, 1837684598⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7749640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15859776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15859776 = ⟨1317259430, 1166571273⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7929888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16023568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16023568 = ⟨699993484, 1207748584⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8011784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16318496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16318496 = ⟨831828675, 1203069593⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8159248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16547856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16547856 = ⟨2069295707, 839059995⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8273928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17367072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17367072 = ⟨1796478570, 1107254111⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8683536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17956928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17956928 = ⟨1697869479, 2045874509⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8978464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18415648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18415648 = ⟨1868932866, 1759894129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9207824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18875392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18875392 = ⟨381944357, 1303428041⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9437696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19136640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19136640 = ⟨261512765, 591027514⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9568320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19464224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19464224 = ⟨58258015, 198537152⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9732112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20054080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20054080 = ⟨1896450489, 166722622⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10027040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20512800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20512800 = ⟨1611268876, 816724647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10256400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21496064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21496064 = ⟨1383721067, 1050466707⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10748032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21561376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21561376 = ⟨1985529309, 1431262010⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10780688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22151232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22151232 = ⟨1781773632, 285630500⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11075616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22609952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22609952 = ⟨378230057, 1722166444⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11304976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23330944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23330944 = ⟨746738648, 1003388758⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11665472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23658528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23658528 = ⟨931638626, 1341415389⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11829264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24248384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24248384 = ⟨645685895, 1856366507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12124192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24707104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24707104 = ⟨161383655, 1003907340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12353552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25755680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25755680 = ⟨1086766960, 179366892⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12877840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26214912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26214912 = ⟨523920845, 1333748616⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13107456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26345536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26345536 = ⟨1738827400, 860169581⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13172768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26804256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26804256 = ⟨609670891, 619682163⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13402128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27525248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27525248 = ⟨2141541873, 78292181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13762624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27852832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27852832 = ⟨2088298597, 1626826103⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13926416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28442688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28442688 = ⟨643018461, 520050684⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14221344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28901408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28901408 = ⟨366909584, 552661025⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14450704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29884672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29884672 = ⟨556064711, 171030911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14942336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29949984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29949984 = ⟨416812072, 337732872⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14974992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30539840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30539840 = ⟨1087771535, 1061550799⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15269920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30998560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30998560 = ⟨119138487, 165900662⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15499280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31719552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31719552 = ⟨513925048, 192671250⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15859776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32047136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32047136 = ⟨1968322956, 1426475967⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16023568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32636992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32636992 = ⟨1325435976, 1172730962⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16318496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33095712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33095712 = ⟨1188758111, 1774846998⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16547856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34734144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34734144 = ⟨1882454280, 711959129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17367072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35913856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35913856 = ⟨952262774, 428537626⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17956928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36831296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36831296 = ⟨586446028, 408296217⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18415648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38273280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38273280 = ⟨1948619399, 986937383⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19136640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38928448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38928448 = ⟨826259914, 341069503⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19464224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40108160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40108160 = ⟨1574485795, 1119756827⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20054080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41025600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41025600 = ⟨168860629, 1137598253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20512800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42992128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42992128 = ⟨312051002, 1260293011⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21496064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43122752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43122752 = ⟨345216596, 783125609⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21561376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44302464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44302464 = ⟨534942251, 1102793351⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22151232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45219904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45219904 = ⟨1302690563, 1909792754⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22609952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46661888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46661888 = ⟨614451501, 1610114679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23330944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47317056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47317056 = ⟨230786217, 1461688747⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23658528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48496768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48496768 = ⟨1888218399, 747294640⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24248384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49414208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49414208 = ⟨565718755, 622088195⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24707104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51511360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51511360 = ⟨576752146, 1455076800⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25755680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52429824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52429824 = ⟨1845204024, 116979180⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26214912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52691072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52691072 = ⟨376971476, 268016479⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26345536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53608512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53608512 = ⟨2034605837, 1789714801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26804256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55050496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55050496 = ⟨94220791, 1956673621⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27525248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55705664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55705664 = ⟨90429605, 256132214⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27852832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56885376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56885376 = ⟨74588835, 275815725⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28442688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57802816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57802816 = ⟨818920529, 447936050⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28901408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59769344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59769344 = ⟨340964709, 1769547956⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29884672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59899968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59899968 = ⟨298610415, 1899547882⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29949984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61079680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61079680 = ⟨718538482, 630623590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30539840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61997120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61997120 = ⟨324934406, 2130114537⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30998560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63439104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63439104 = ⟨546145192, 453818720⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31719552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64094272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64094272 = ⟨475026732, 81176039⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32047136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65273984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65273984 = ⟨1531118290, 1394880236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32636992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66191424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66191424 = ⟨1402028325, 650270718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33095712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69468288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69468288 = ⟨462893649, 715594177⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34734144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71827712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71827712 = ⟨548922351, 1065252843⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35913856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73662592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73662592 = ⟨661284595, 716999406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36831296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76546560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76546560 = ⟨1620103066, 1042089945⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38273280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77856896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77856896 = ⟨1047067320, 1585651127⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38928448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_80216320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 80216320 = ⟨422004508, 72347641⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40108160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_82051200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 82051200 = ⟨2089579378, 821343858⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41025600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_85984256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 85984256 = ⟨1589276025, 1583924546⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42992128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_86245504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86245504 = ⟨1075489131, 973541643⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43122752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88604928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88604928 = ⟨849659428, 520646898⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44302464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90439808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90439808 = ⟨338141168, 1136659037⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45219904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_93323776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93323776 = ⟨1827714321, 1157118019⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46661888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94634112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94634112 = ⟨1846957610, 1119950559⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47317056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_96993536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96993536 = ⟨1015268188, 631143063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48496768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98828416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98828416 = ⟨2073083128, 1822435363⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49414208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_103022720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103022720 = ⟨1382414041, 2093650617⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51511360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105382144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105382144 = ⟨2110707499, 1592581877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52691072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_107217024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 107217024 = ⟨963762808, 950413619⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53608512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_110100992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110100992 = ⟨1440293118, 1753982305⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55050496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_111411328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 111411328 = ⟨1918757455, 1913947836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55705664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_113770752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 113770752 = ⟨1812363120, 1046509214⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56885376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115605632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115605632 = ⟨272916483, 940711341⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57802816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_119538688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119538688 = ⟨15470579, 1643565293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59769344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_119799936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119799936 = ⟨2062003763, 9729192⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59899968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122159360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122159360 = ⟨1856602386, 1633382507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61079680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123994240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123994240 = ⟨73462450, 1466353373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61997120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126878208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126878208 = ⟨639203600, 1206762077⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63439104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_128188544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128188544 = ⟨2083729018, 1853384892⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64094272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_130547968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 130547968 = ⟨235585207, 1177496435⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65273984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_132382848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 132382848 = ⟨572107093, 2033478988⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66191424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_138936576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 138936576 = ⟨46691047, 1843327688⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69468288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_143655424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 143655424 = ⟨1711367822, 691951232⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71827712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_147325184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 147325184 = ⟨25916335, 202332546⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73662592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_153093120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 153093120 = ⟨2095613886, 527857063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76546560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_155713792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 155713792 = ⟨1391712886, 392048426⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77856896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_160432640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 160432640 = ⟨1987304903, 170425270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80216320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_164102400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 164102400 = ⟨1138798876, 1372748451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82051200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_172491008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 172491008 = ⟨1944732514, 113509048⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86245504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_177209856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 177209856 = ⟨923437041, 531929602⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88604928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_180879616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 180879616 = ⟨1148247677, 1520364018⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90439808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_186647552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 186647552 = ⟨1766982315, 596409291⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93323776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_189268224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 189268224 = ⟨1171082692, 669024443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94634112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_193987072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 193987072 = ⟨62042034, 1522937005⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96993536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_197656832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 197656832 = ⟨1401683502, 1281008138⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98828416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_206045440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 206045440 = ⟨1553298144, 1275897505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103022720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_210764288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 210764288 = ⟨1869158254, 284678487⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105382144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_214434048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 214434048 = ⟨1146144815, 1641037634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_107217024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_220201984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 220201984 = ⟨820025422, 857904003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110100992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_222822656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 222822656 = ⟨739517772, 258920324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111411328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_227541504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 227541504 = ⟨1481143745, 190825439⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_113770752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_231211264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 231211264 = ⟨257358111, 1490477270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115605632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_239599872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 239599872 = ⟨1361922852, 839381689⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119799936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_244318720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 244318720 = ⟨84326181, 1640278033⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122159360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_247988480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 247988480 = ⟨2004269240, 1856057691⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123994240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_253756416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 253756416 = ⟨1399753701, 1692335411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126878208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_256377088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 256377088 = ⟨1797169487, 1102120522⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128188544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_261095936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 261095936 = ⟨1943339742, 1683025006⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_130547968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_264765696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 264765696 = ⟨1063385765, 2123063218⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_132382848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_277873152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 277873152 = ⟨824447966, 1440438910⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_138936576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_287310848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 287310848 = ⟨1593271412, 1557280492⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_143655424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_294650368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 294650368 = ⟨1688923833, 2128457796⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_147325184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_311427584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 311427584 = ⟨140959160, 53262469⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_155713792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_320865280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 320865280 = ⟨1158837492, 819566845⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_160432640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_328204800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 328204800 = ⟨1863122379, 967300390⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_164102400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_344982016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 344982016 = ⟨1807359661, 471817612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_172491008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_354419712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 354419712 = ⟨425606435, 736395182⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_177209856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_361759232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 361759232 = ⟨1990898152, 1100535815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_180879616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_378536448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 378536448 = ⟨1664106084, 1110545074⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_189268224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_387974144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 387974144 = ⟨1886413538, 1618829578⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_193987072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_395313664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 395313664 = ⟨431418887, 547791316⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_197656832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_412090880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 412090880 = ⟨1585942335, 2012791612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_206045440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_421528576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 421528576 = ⟨2125667422, 1995711117⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_210764288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_428868096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 428868096 = ⟨750715036, 1324815284⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_214434048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_445645312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 445645312 = ⟨284808895, 151546026⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_222822656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_455083008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 455083008 = ⟨1060867294, 1016052282⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_227541504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_462422528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 462422528 = ⟨1848630904, 1048434451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_231211264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_479199744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 479199744 = ⟨2019754080, 1626612110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_239599872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_488637440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 488637440 = ⟨367584259, 2107277889⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_244318720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_495976960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 495976960 = ⟨483419048, 655274775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_247988480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_512754176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 512754176 = ⟨798713547, 2021022909⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_256377088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_522191872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 522191872 = ⟨1150072909, 950473072⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_261095936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_529531392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 529531392 = ⟨2007423013, 1959260283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_264765696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_555746304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 555746304 = ⟨1303428041, 1765539290⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_277873152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_589300736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 589300736 = ⟨116979180, 302279623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_294650368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_622855168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 622855168 = ⟨1583924546, 558207622⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_311427584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_656409600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 656409600 = ⟨1643565293, 2132013068⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_328204800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_689964032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 689964032 = ⟨527857063, 51869761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_344982016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_723518464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 723518464 = ⟨596409291, 380501332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_361759232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_757072896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 757072896 = ⟨857904003, 1327458225⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_378536448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_790627328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 790627328 = ⟨1692335411, 747729946⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_395313664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_824181760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 824181760 = ⟨1557280492, 554212235⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_412090880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_857736192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 857736192 = ⟨819566845, 988646155⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_428868096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_891290624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 891290624 = ⟨736395182, 1721877212⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_445645312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_924845056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 924845056 = ⟨1618829578, 261070109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_462422528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_958399488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 958399488 = ⟨1995711117, 21816225⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_479199744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_991953920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 991953920 = ⟨1016052282, 1086616353⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_495976960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1025508352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1025508352 = ⟨2107277889, 1779899388⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_512754176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1059062784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1059062784 = ⟨950473072, 997410738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_529531392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 288) = ⟨381944357, 1303428041⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 288 = 18875392 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_18875392

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨381944357, 1303428041⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 288) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 289) = ⟨1303428041, 1765539290⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 289 = 555746304 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_555746304

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1303428041, 1765539290⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 289) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 290) = ⟨1593271412, 1557280492⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 290 = 287310848 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_287310848

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1593271412, 1557280492⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 290) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 291) = ⟨1557280492, 554212235⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 291 = 824181760 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_824181760

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1557280492, 554212235⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 291) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 292) = ⟨2095613886, 527857063⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 292 = 153093120 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_153093120

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2095613886, 527857063⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 292) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 293) = ⟨527857063, 51869761⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 293 = 689964032 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_689964032

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨527857063, 51869761⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 293) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 294) = ⟨2125667422, 1995711117⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 294 = 421528576 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_421528576

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2125667422, 1995711117⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 294) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 295) = ⟨1995711117, 21816225⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 295 = 958399488 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_958399488

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1995711117, 21816225⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 295) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 296) = ⟨1589276025, 1583924546⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 296 = 85984256 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_85984256

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1589276025, 1583924546⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 296) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 297) = ⟨1583924546, 558207622⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 297 = 622855168 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_622855168

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1583924546, 558207622⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 297) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 298) = ⟨425606435, 736395182⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 298 = 354419712 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_354419712

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨425606435, 736395182⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 298) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 299) = ⟨736395182, 1721877212⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 299 = 891290624 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_891290624

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨736395182, 1721877212⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 299) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 300) = ⟨820025422, 857904003⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 300 = 220201984 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_220201984

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨820025422, 857904003⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 300) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 301) = ⟨857904003, 1327458225⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 301 = 757072896 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_757072896

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨857904003, 1327458225⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 301) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 302) = ⟨367584259, 2107277889⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 302 = 488637440 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_488637440

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨367584259, 2107277889⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 302) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 303) = ⟨2107277889, 1779899388⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 303 = 1025508352 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1025508352

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2107277889, 1779899388⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 303) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 304) = ⟨1845204024, 116979180⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 304 = 52429824 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_52429824

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1845204024, 116979180⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 304) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 305) = ⟨116979180, 302279623⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 305 = 589300736 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_589300736

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨116979180, 302279623⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 305) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 306) = ⟨1158837492, 819566845⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 306 = 320865280 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_320865280

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1158837492, 819566845⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 306) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 307) = ⟨819566845, 988646155⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 307 = 857736192 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_857736192

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨819566845, 988646155⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 307) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 308) = ⟨1766982315, 596409291⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 308 = 186647552 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_186647552

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1766982315, 596409291⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 308) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 309) = ⟨596409291, 380501332⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 309 = 723518464 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_723518464

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨596409291, 380501332⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 309) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 310) = ⟨1060867294, 1016052282⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 310 = 455083008 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_455083008

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1060867294, 1016052282⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 310) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 311) = ⟨1016052282, 1086616353⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 311 = 991953920 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_991953920

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1016052282, 1086616353⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 311) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 312) = ⟨15470579, 1643565293⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 312 = 119538688 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_119538688

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨15470579, 1643565293⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 312) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 313) = ⟨1643565293, 2132013068⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 313 = 656409600 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_656409600

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1643565293, 2132013068⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 313) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 314) = ⟨1886413538, 1618829578⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 314 = 387974144 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_387974144

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1886413538, 1618829578⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 314) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 315) = ⟨1618829578, 261070109⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 315 = 924845056 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_924845056

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1618829578, 261070109⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 315) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 316) = ⟨1399753701, 1692335411⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 316 = 253756416 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_253756416

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1399753701, 1692335411⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 316) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 317) = ⟨1692335411, 747729946⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 317 = 790627328 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_790627328

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1692335411, 747729946⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 317) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 318) = ⟨1150072909, 950473072⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 318 = 522191872 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_522191872

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1150072909, 950473072⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 318) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 319) = ⟨950473072, 997410738⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 319 = 1059062784 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1059062784

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨950473072, 997410738⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 319) := by
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

end R17TableAChunk09Certificate
