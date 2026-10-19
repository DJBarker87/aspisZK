import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableBChunk09Certificate
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

theorem power_18432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18432 = ⟨1139757936, 161139962⟩ := by
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

theorem power_36864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36864 = ⟨1421883301, 1767600112⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18432]
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

theorem power_51200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51200 = ⟨687167191, 1193781868⟩ := by
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

theorem power_83968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83968 = ⟨1235766230, 338243230⟩ := by
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

theorem power_102400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102400 = ⟨606906923, 1264738384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51200]
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

theorem power_116736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116736 = ⟨342937346, 440901543⟩ := by
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

theorem power_149504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 149504 = ⟨1071628068, 1255434837⟩ := by
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

theorem power_167936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 167936 = ⟨729011542, 952009042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83968]
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

theorem power_182272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 182272 = ⟨1309999598, 467334114⟩ := by
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

theorem power_215040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 215040 = ⟨511564144, 1485902172⟩ := by
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

theorem power_233472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 233472 = ⟨953139263, 265503960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116736]
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

theorem power_247808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 247808 = ⟨1752942601, 1104368066⟩ := by
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

theorem power_280576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 280576 = ⟨301592792, 2080568233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_140288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_287744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 287744 = ⟨179957683, 618553811⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_143872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_299008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 299008 = ⟨1318914216, 1663922738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_149504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_304128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 304128 = ⟨1877383557, 1174650430⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_152064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_313344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 313344 = ⟨1519289632, 554415477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_156672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_320512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 320512 = ⟨1569243112, 1043148296⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_160256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_336896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 336896 = ⟨1048079598, 1664012201⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_168448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_346112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 346112 = ⟨1396387241, 1636248379⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_173056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_353280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 353280 = ⟨1432115175, 1175896303⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_176640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_364544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 364544 = ⟨291679777, 1578449442⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_182272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_369664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 369664 = ⟨73683083, 1009582096⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_184832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_378880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 378880 = ⟨796901153, 679264882⟩ := by
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

theorem power_411648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 411648 = ⟨1993145094, 1556913362⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_205824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_418816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 418816 = ⟨1739022919, 299936075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_209408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_430080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 430080 = ⟨782570832, 476532960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_215040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_435200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 435200 = ⟨238661036, 428034347⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_217600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_444416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 444416 = ⟨833065953, 160077459⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_222208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_451584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 451584 = ⟨2081843833, 1308756649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_225792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_467968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 467968 = ⟨1597597014, 843895897⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_233984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_477184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 477184 = ⟨1762390813, 1601969049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_238592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_484352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 484352 = ⟨1285025349, 1411487338⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_242176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_495616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 495616 = ⟨1954241062, 1820169310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_247808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_500736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 500736 = ⟨1012753014, 1231443995⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_250368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_509952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 509952 = ⟨1277755557, 2036963937⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_254976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_517120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 517120 = ⟨116962009, 1390307281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_258560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_542720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 542720 = ⟨956657888, 291038160⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_271360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_561152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 561152 = ⟨848823435, 1634673682⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_280576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_575488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 575488 = ⟨471311722, 784900931⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_287744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_608256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 608256 = ⟨1572839832, 1327270854⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_304128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_626688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 626688 = ⟨1771477961, 772209956⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_313344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_641024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 641024 = ⟨359306860, 804380630⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_320512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_673792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 673792 = ⟨1743622189, 1434497021⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_336896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_692224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 692224 = ⟨1079208008, 2008108071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_346112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_706560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 706560 = ⟨1447523228, 863369865⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_353280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_739328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 739328 = ⟨1009483326, 159986540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_369664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_757760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 757760 = ⟨1109468214, 24685739⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_378880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_772096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 772096 = ⟨1277257384, 687295715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_386048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_804864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 804864 = ⟨847375021, 1683564466⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_402432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_823296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 823296 = ⟨2079323762, 1208852267⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_411648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_837632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 837632 = ⟨681138556, 1124705724⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_418816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_870400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 870400 = ⟨1006454549, 136324594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_435200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_888832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 888832 = ⟨1954195642, 800757595⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_444416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_903168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 903168 = ⟨1388297937, 319639269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_451584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_935936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 935936 = ⟨1182829080, 1403391250⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_467968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_954368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 954368 = ⟨1462196868, 1013065725⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_477184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_968704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 968704 = ⟨838794177, 327403577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_484352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1001472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1001472 = ⟨941931943, 1990652193⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_500736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1019904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1019904 = ⟨878071934, 497955134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_509952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1034240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1034240 = ⟨1535598549, 1063355251⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_517120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1085440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1085440 = ⟨1742158212, 947474543⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_542720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1150976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1150976 = ⟨875583808, 1932435950⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_575488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1216512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1216512 = ⟨1995718635, 990602029⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_608256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1282048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1282048 = ⟨1255153497, 1873206092⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_641024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1347584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1347584 = ⟨500001204, 1350892375⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_673792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1413120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1413120 = ⟨1036739736, 4090232⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_706560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1478656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1478656 = ⟨649844810, 475157379⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_739328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1544192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1544192 = ⟨461636029, 555407991⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_772096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1609728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1609728 = ⟨47282233, 1973840192⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_804864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1675264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1675264 = ⟨1153435498, 735309441⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_837632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1740800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1740800 = ⟨985150678, 1044660427⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_870400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1806336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1806336 = ⟨1194288306, 1664016260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_903168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1871872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1871872 = ⟨1386607805, 2069854787⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_935936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1937408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1937408 = ⟨3045475, 162418948⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_968704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2002944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2002944 = ⟨405825245, 2000126861⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1001472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2068480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2068480 = ⟨1274127696, 398642911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1034240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 288) = ⟨1421883301, 1767600112⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 288 = 36864 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_36864

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1421883301, 1767600112⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 288) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 289) = ⟨1742158212, 947474543⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 289 = 1085440 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1085440

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1742158212, 947474543⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 289) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 290) = ⟨848823435, 1634673682⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 290 = 561152 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_561152

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨848823435, 1634673682⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 290) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 291) = ⟨47282233, 1973840192⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 291 = 1609728 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1609728

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨47282233, 1973840192⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 291) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 292) = ⟨1318914216, 1663922738⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 292 = 299008 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_299008

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1318914216, 1663922738⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 292) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 293) = ⟨500001204, 1350892375⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 293 = 1347584 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1347584

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨500001204, 1350892375⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 293) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 294) = ⟨2079323762, 1208852267⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 294 = 823296 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_823296

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2079323762, 1208852267⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 294) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 295) = ⟨1386607805, 2069854787⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 295 = 1871872 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1871872

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1386607805, 2069854787⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 295) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 296) = ⟨729011542, 952009042⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 296 = 167936 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_167936

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨729011542, 952009042⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 296) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 297) = ⟨1995718635, 990602029⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 297 = 1216512 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1216512

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1995718635, 990602029⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 297) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 298) = ⟨1079208008, 2008108071⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 298 = 692224 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_692224

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1079208008, 2008108071⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 298) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 299) = ⟨985150678, 1044660427⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 299 = 1740800 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1740800

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨985150678, 1044660427⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 299) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 300) = ⟨782570832, 476532960⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 300 = 430080 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_430080

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨782570832, 476532960⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 300) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 301) = ⟨649844810, 475157379⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 301 = 1478656 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1478656

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨649844810, 475157379⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 301) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 302) = ⟨1462196868, 1013065725⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 302 = 954368 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_954368

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1462196868, 1013065725⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 302) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 303) = ⟨405825245, 2000126861⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 303 = 2002944 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2002944

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨405825245, 2000126861⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 303) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 304) = ⟨606906923, 1264738384⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 304 = 102400 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_102400

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨606906923, 1264738384⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 304) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 305) = ⟨875583808, 1932435950⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 305 = 1150976 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1150976

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨875583808, 1932435950⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 305) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 306) = ⟨1771477961, 772209956⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 306 = 626688 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_626688

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1771477961, 772209956⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 306) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 307) = ⟨1153435498, 735309441⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 307 = 1675264 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1675264

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1153435498, 735309441⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 307) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 308) = ⟨291679777, 1578449442⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 308 = 364544 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_364544

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨291679777, 1578449442⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 308) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 309) = ⟨1036739736, 4090232⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 309 = 1413120 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1413120

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1036739736, 4090232⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 309) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 310) = ⟨1954195642, 800757595⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 310 = 888832 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_888832

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1954195642, 800757595⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 310) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 311) = ⟨3045475, 162418948⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 311 = 1937408 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1937408

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨3045475, 162418948⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 311) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 312) = ⟨953139263, 265503960⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 312 = 233472 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_233472

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨953139263, 265503960⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 312) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 313) = ⟨1255153497, 1873206092⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 313 = 1282048 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1282048

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1255153497, 1873206092⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 313) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 314) = ⟨1109468214, 24685739⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 314 = 757760 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_757760

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1109468214, 24685739⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 314) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 315) = ⟨1194288306, 1664016260⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 315 = 1806336 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1806336

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1194288306, 1664016260⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 315) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 316) = ⟨1954241062, 1820169310⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 316 = 495616 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_495616

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1954241062, 1820169310⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 316) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 317) = ⟨461636029, 555407991⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 317 = 1544192 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1544192

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨461636029, 555407991⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 317) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 318) = ⟨878071934, 497955134⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 318 = 1019904 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1019904

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨878071934, 497955134⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 318) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 319) = ⟨1274127696, 398642911⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 319 = 2068480 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2068480

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1274127696, 398642911⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 319) := by
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

end R17TableBChunk09Certificate
