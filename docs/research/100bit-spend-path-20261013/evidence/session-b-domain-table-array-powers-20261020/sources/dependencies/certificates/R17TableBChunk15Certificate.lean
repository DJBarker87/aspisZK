import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableBChunk15Certificate
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

theorem power_53 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53 = ⟨229109997, 409681538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26]
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

theorem power_67 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67 = ⟨1982486292, 1611456260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33]
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

theorem power_87 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87 = ⟨1648565317, 52537112⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_91 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 91 = ⟨924358641, 1577205411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45]
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

theorem power_103 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103 = ⟨2138693243, 755167780⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_107 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 107 = ⟨1286380731, 398286559⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53]
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

theorem power_119 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119 = ⟨2017000003, 1501730632⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120 = ⟨1743886464, 1431800964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123 = ⟨830648882, 1820319682⟩ := by
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

theorem power_127 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 127 = ⟨215093227, 1600453215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_135 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 135 = ⟨1083123019, 1628198916⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_143 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 143 = ⟨649500112, 2034135325⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_151 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 151 = ⟨1692705482, 1818541172⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_158 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 158 = ⟨489525484, 1281277745⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_159 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 159 = ⟨1821188515, 935469127⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_167 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 167 = ⟨2122757670, 2074642722⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_175 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 175 = ⟨1796779512, 105776642⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_183 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 183 = ⟨59803849, 1583788062⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_188 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 188 = ⟨528927296, 843766190⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_190 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 190 = ⟨440498398, 1405716006⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_95]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_191 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 191 = ⟨445895345, 765526181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_95]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_199 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 199 = ⟨328392223, 1882866834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_207 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 207 = ⟨1646120199, 674488163⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_215 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 215 = ⟨1298411934, 695435615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_107]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_222 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 222 = ⟨727910565, 2105491058⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_223 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 223 = ⟨1093183766, 2113724405⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_231 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 231 = ⟨235212131, 119569981⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_239 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 239 = ⟨1100045001, 952183731⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 240 = ⟨545370846, 562844461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_247 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 247 = ⟨1816092284, 1450828631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 248 = ⟨1426926249, 1272112238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_252 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 252 = ⟨1105406260, 2088944411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_254 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 254 = ⟨1336163041, 934467179⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_127]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_255 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 255 = ⟨2049905280, 1908273995⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_127]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_271 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 271 = ⟨945822274, 642907872⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_135]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_286 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 286 = ⟨1312976075, 1874233770⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_143]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_287 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 287 = ⟨1159793934, 1400273155⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_143]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_303 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 303 = ⟨1546898200, 1943309608⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_151]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_316 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 316 = ⟨122822374, 1506996359⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_158]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_318 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 318 = ⟨1813013584, 1649406943⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_159]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_319 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 319 = ⟨1399386229, 439817829⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_159]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_335 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 335 = ⟨233478879, 750828529⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_167]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_350 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 350 = ⟨2091438009, 37173329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_175]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_351 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 351 = ⟨1590237515, 911535235⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_175]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_367 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 367 = ⟨1342589108, 1890994059⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_183]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 376 = ⟨1159319502, 1675729942⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_188]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_380 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 380 = ⟨1851733557, 955506512⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_190]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_382 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 382 = ⟨1013132639, 304243825⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_191]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_383 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 383 = ⟨1188830360, 365166804⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_191]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_399 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 399 = ⟨410184019, 1644661100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_199]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_414 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 414 = ⟨2113912359, 1823140805⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_207]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_415 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 415 = ⟨1495220671, 199377078⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_207]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_431 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 431 = ⟨1122797149, 752578727⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_215]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_444 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 444 = ⟨1497047437, 657280689⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_222]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_446 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 446 = ⟨661835025, 1845286520⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_223]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_447 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 447 = ⟨1033877661, 1923666072⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_223]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_463 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 463 = ⟨2036662303, 831141537⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_231]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_478 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 478 = ⟨1458859561, 318476705⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_239]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_479 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 479 = ⟨976782905, 1117430647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_239]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 480 = ⟨300788412, 2003762236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_495 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 495 = ⟨924704314, 1188869220⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_247]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 496 = ⟨496157480, 1934975487⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 504 = ⟨1166538521, 799975189⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_252]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_508 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 508 = ⟨448825931, 2045579845⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_254]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_510 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 510 = ⟨32512296, 517576488⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_255]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_511 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 511 = ⟨546585539, 892645957⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_255]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_542 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 542 = ⟨1510715465, 869152059⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_271]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_572 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 572 = ⟨1434583057, 1273507208⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_286]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_574 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 574 = ⟨523775679, 1412194024⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_287]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_606 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 606 = ⟨506672719, 1955016540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_303]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 632 = ⟨1190907240, 1512712836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_316]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_636 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 636 = ⟨420776129, 845069566⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_318]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_638 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 638 = ⟨713819826, 311575904⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_319]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_670 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 670 = ⟨1237370729, 1916048645⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_335]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_700 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 700 = ⟨2039040404, 1736652883⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_350]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_702 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 702 = ⟨686598689, 1445043794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_351]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_734 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 734 = ⟨1580938111, 1342551559⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_367]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 752 = ⟨1618036228, 1571179552⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 760 = ⟨1677239789, 1455954222⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_380]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_764 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 764 = ⟨134455620, 1163435542⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_382]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_766 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 766 = ⟨1599580176, 761829412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_383]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_798 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 798 = ⟨1853841185, 313297504⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_399]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_828 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 828 = ⟨1643040924, 1014125157⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_414]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_830 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 830 = ⟨308549409, 1763273565⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_415]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_862 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 862 = ⟨838220497, 1345241310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_431]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 888 = ⟨120585028, 1684505782⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_444]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_892 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 892 = ⟨52506139, 1639713130⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_446]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_894 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 894 = ⟨262547224, 1243703142⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_447]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_926 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 926 = ⟨858689372, 712685693⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_463]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_956 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 956 = ⟨1766003384, 644713738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_478]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_958 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 958 = ⟨1536562836, 950294048⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_479]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 960 = ⟨418523497, 1921984699⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_990 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 990 = ⟨999337515, 2022566501⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_495]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 992 = ⟨175521256, 1612727439⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1008 = ⟨1430834825, 343589054⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1016 = ⟨2040043404, 655505031⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_508]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1020 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1020 = ⟨2063643140, 1601449715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_510]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1022 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1022 = ⟨1600946216, 1397815243⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_511]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1084 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1084 = ⟨1711655825, 1824582820⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_542]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1144 = ⟨684087935, 140548154⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_572]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1148 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1148 = ⟨191693724, 1793089654⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_574]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1212 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1212 = ⟨1950287013, 420390807⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_606]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1264 = ⟨1815749764, 1026740353⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1272 = ⟨1010783342, 1393820171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_636]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1276 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1276 = ⟨302162606, 469866736⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_638]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1340 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1340 = ⟨178707896, 1407975338⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_670]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1400 = ⟨1642577879, 155228252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_700]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1404 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1404 = ⟨1979379794, 422788357⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_702]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1468 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1468 = ⟨545902602, 759025140⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_734]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1504 = ⟨1454439079, 540218179⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1520 = ⟨94356015, 60988031⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1528 = ⟨1532894372, 1797171798⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_764]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1532 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1532 = ⟨544388350, 1491056578⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_766]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1596 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1596 = ⟨49666306, 1252828345⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_798]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1656 = ⟨502735259, 193158691⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_828]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1660 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1660 = ⟨1963380235, 1018423263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_830]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1724 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1724 = ⟨1499429541, 16501644⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_862]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1776 = ⟨1677424398, 257293674⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1784 = ⟨447650615, 522686506⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_892]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1788 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1788 = ⟨369374765, 841793352⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_894]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1852 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1852 = ⟨597567609, 1597305399⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_926]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1912 = ⟨679289911, 1807755185⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_956]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1916 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1916 = ⟨1642838862, 996119707⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_958]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1920 = ⟨203869561, 313423390⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1980 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1980 = ⟨690814626, 438396262⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_990]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1984 = ⟨57053772, 179506272⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2016 = ⟨218579473, 733898632⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2032 = ⟨921915899, 1623882885⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2040 = ⟨335137890, 1180677973⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1020]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2044 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2044 = ⟨840360168, 983162554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1022]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2168 = ⟨1706363302, 1167948779⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1084]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2288 = ⟨853372384, 1508779871⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2296 = ⟨2010398988, 1598615695⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1148]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2424 = ⟨1975243669, 1140194470⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1212]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2528 = ⟨420427824, 553428442⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2544 = ⟨749714304, 2116546729⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2552 = ⟨1497552932, 1130184832⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1276]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2680 = ⟨1460945113, 18528046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1340]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2800 = ⟨2102317524, 705206869⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2808 = ⟨1157696285, 628421000⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1404]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2936 = ⟨940800402, 2108221798⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1468]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3008 = ⟨327335145, 1879026140⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3040 = ⟨1071189603, 670105011⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3056 = ⟨1236844022, 1218587997⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3064 = ⟨1959778971, 1278253742⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1532]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3192 = ⟨1001641467, 193098788⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1596]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3312 = ⟨84826221, 1783037972⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3320 = ⟨246434564, 1679042905⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1660]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3448 = ⟨1933408317, 769487147⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1724]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3552 = ⟨500555238, 550603101⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3568 = ⟨484378139, 1504174011⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3576 = ⟨2035346774, 1878019669⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1788]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3704 = ⟨928421245, 1184785247⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1852]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3824 = ⟨1061710231, 784310051⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3832 = ⟨575671186, 1992461928⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1916]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3840 = ⟨2080156404, 1988869649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3960 = ⟨1818854120, 1868202233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1980]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3968 = ⟨1619251001, 830366565⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4032 = ⟨1385987562, 2130936594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4064 = ⟨1890832283, 1131752619⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4080 = ⟨299682654, 1154018467⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4088 = ⟨1109486615, 444488181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2044]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4336 = ⟨1674810838, 1910681140⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4576 = ⟨1883111880, 197853127⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4592 = ⟨1227506420, 171887912⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4848 = ⟨1370410566, 1851449991⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5056 = ⟨230291843, 2009340597⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5088 = ⟨1675363414, 2024500035⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5104 = ⟨1587001620, 1862675805⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5360 = ⟨1462077080, 529675894⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5600 = ⟨397407191, 173471874⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5616 = ⟨1003569804, 1689459083⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5872 = ⟨2079377715, 881503593⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6016 = ⟨34128733, 779289293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6080 = ⟨2096900361, 460487749⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6112 = ⟨706074471, 570762835⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6128 = ⟨1205915441, 1790914690⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6384 = ⟨2070729739, 875053313⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6624 = ⟨424967641, 588853096⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6640 = ⟨1515566733, 506693267⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6896 = ⟨1989648439, 1488204562⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7104 = ⟨1208905995, 1975255680⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7136 = ⟨593804343, 539088081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7152 = ⟨1636243850, 1238229684⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7408 = ⟨711377955, 691881972⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7648 = ⟨59592689, 1115813540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7664 = ⟨435236591, 248726258⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7680 = ⟨1699022782, 2146531477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7920 = ⟨36023362, 1609102644⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7936 = ⟨162722436, 856104198⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8064 = ⟨551499030, 172901195⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8128 = ⟨2092130176, 1007498697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8160 = ⟨1396224713, 473101775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8176 = ⟨326620293, 2133132463⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8672 = ⟨1352855767, 1495199328⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9152 = ⟨2124389071, 474079624⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9184 = ⟨919205316, 374741552⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9696 = ⟨452578781, 144807757⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10112 = ⟨1140710360, 603015796⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10176 = ⟨194329488, 1475749982⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10208 = ⟨580577914, 978699981⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10720 = ⟨1947275373, 733837589⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11200 = ⟨1563170848, 460055775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11232 = ⟨1001486344, 572782889⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11744 = ⟨797396886, 607136852⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12032 = ⟨2111712505, 1478380338⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12160 = ⟨78431529, 1330433026⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12224 = ⟨1274349836, 578895393⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12256 = ⟨664432675, 84270675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12768 = ⟨1138456843, 1519209408⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13248 = ⟨1989260733, 321002215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13280 = ⟨1059002249, 1817848256⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13792 = ⟨235806119, 1490999069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14208 = ⟨1331555980, 1659587301⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14272 = ⟨1380217867, 2049539467⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14304 = ⟨550444898, 982477159⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14816 = ⟨1483390978, 514964477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15296 = ⟨487831876, 2068089277⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15328 = ⟨867532753, 1881955433⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15360 = ⟨1368263916, 2076980552⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15840 = ⟨235664120, 836504396⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15872 = ⟨1544810668, 1648948073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16128 = ⟨529431379, 793096648⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16256 = ⟨1413056715, 1060691396⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16320 = ⟨30377366, 253029684⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16352 = ⟨168894653, 1737998913⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17344 = ⟨184066578, 1387394275⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18304 = ⟨1476748888, 884639226⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18368 = ⟨1113114665, 1953962952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19392 = ⟨239740893, 784196317⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20224 = ⟨1941045180, 67585795⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20352 = ⟨152046194, 216016803⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20416 = ⟨1171035236, 727647520⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21440 = ⟨1099791594, 1519964390⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22400 = ⟨573590654, 1886827735⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22464 = ⟨2119967210, 1818220486⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23488 = ⟨1563407039, 1464315291⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24064 = ⟨1527773015, 1087146275⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24320 = ⟨506965036, 1359957011⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24448 = ⟨213493885, 1016706441⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24512 = ⟨586610408, 1260068120⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25536 = ⟨1879917313, 1413641359⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26496 = ⟨367539449, 193384522⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26560 = ⟨82908178, 861836318⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27584 = ⟨243054071, 908694224⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28416 = ⟨309176294, 1806259591⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28544 = ⟨916693893, 1949733986⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28608 = ⟨427524280, 1676336671⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29632 = ⟨1568424475, 1554908389⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30592 = ⟨1770822168, 126575104⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30656 = ⟨813520814, 154830994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30720 = ⟨1155186462, 790771269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31680 = ⟨1390992646, 1932199123⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31744 = ⟨2081374532, 23687746⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32256 = ⟨1518927485, 1630959494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32512 = ⟨1171512511, 1682664880⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32640 = ⟨1956611288, 1837317070⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32704 = ⟨1143535073, 1469219745⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34688 = ⟨618072854, 485674286⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36608 = ⟨1237538406, 1195917052⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36736 = ⟨2116535582, 466340540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38784 = ⟨2132996333, 1831647709⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40448 = ⟨1678099002, 1435930170⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40704 = ⟨648199292, 1726925026⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40832 = ⟨1189559306, 1517688310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42880 = ⟨412330574, 1877226017⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44800 = ⟨242848192, 1491966760⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44928 = ⟨1926733299, 689976827⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46976 = ⟨1368332297, 1180683767⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48128 = ⟨199715453, 200523046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48640 = ⟨195735798, 904617319⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48896 = ⟨1503941587, 812496302⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49024 = ⟨991921107, 808916205⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51072 = ⟨1131772229, 2073265359⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52992 = ⟨1477173668, 1592872585⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53120 = ⟨927944996, 1424289211⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55168 = ⟨478538560, 1402343432⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56832 = ⟨88223642, 1372710776⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57088 = ⟨776408200, 1907239669⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57216 = ⟨1295414114, 659610540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59264 = ⟨2063724304, 1853090895⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61184 = ⟨1544835842, 1484496856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61312 = ⟨547646855, 2046221276⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61440 = ⟨1168068815, 1631133982⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63360 = ⟨1322171884, 737849280⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63488 = ⟨498226347, 579000983⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64512 = ⟨195756815, 1145261885⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65024 = ⟨2056601171, 1788969342⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65280 = ⟨1728232360, 1687432543⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65408 = ⟨1569195062, 1729184480⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69376 = ⟨873630414, 2068516862⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73216 = ⟨639455891, 1442019586⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73472 = ⟨1451429861, 903567614⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77568 = ⟨200357395, 2128797380⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_80896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 80896 = ⟨261220802, 1540312068⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_81408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81408 = ⟨1723831742, 42601928⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_81664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81664 = ⟨248412051, 2041644625⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_85760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 85760 = ⟨1462727669, 780147914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89600 = ⟨943470255, 773386671⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89856 = ⟨89055855, 381830750⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_93952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93952 = ⟨76469608, 721118345⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_96256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96256 = ⟨838488945, 628575040⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_97280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 97280 = ⟨1278659801, 828728392⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_97792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 97792 = ⟨1831055074, 2137864713⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98048 = ⟨479554147, 1445433846⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102144 = ⟨673408698, 1384679542⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105984 = ⟨1326715095, 1134353850⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106240 = ⟨2074890209, 463152412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_110336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110336 = ⟨504587792, 1510425115⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_113664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 113664 = ⟨821194025, 337743815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_114176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114176 = ⟨1234207074, 1328414378⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_114432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114432 = ⟨131700479, 323187478⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_118528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118528 = ⟨657010933, 1486957677⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122368 = ⟨183438626, 1151491724⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122624 = ⟨407801434, 1235878211⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126720 = ⟨1786195431, 1289560474⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126976 = ⟨1029759507, 977441374⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_129024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 129024 = ⟨1111967682, 967749599⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_130048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 130048 = ⟨1516173173, 5998182⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_130560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 130560 = ⟨1982498978, 1176705856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_130816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 130816 = ⟨1939072022, 1778341668⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_138752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 138752 = ⟨718512757, 773081674⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_146432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 146432 = ⟨2123620430, 1690710365⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_146944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 146944 = ⟨933661902, 328991836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_155136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 155136 = ⟨2090762882, 1750923493⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_161792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 161792 = ⟨1110908996, 694969566⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_162816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 162816 = ⟨120216793, 1836770504⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_163328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 163328 = ⟨2085153587, 2008014224⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_171520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 171520 = ⟨331167587, 949565468⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_179200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 179200 = ⟨752234394, 244937601⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_179712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 179712 = ⟨877202653, 1340225614⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_187904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 187904 = ⟨1658818033, 345590962⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_192512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 192512 = ⟨1389630114, 73256692⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_194560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 194560 = ⟨699364689, 518616269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_97280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_195584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 195584 = ⟨883269279, 1501677227⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_97792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_196096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 196096 = ⟨1672240763, 1179717494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_204288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 204288 = ⟨1498796612, 522932198⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_211968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 211968 = ⟨186431743, 1909359341⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_212480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 212480 = ⟨965044857, 1117192690⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_220672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 220672 = ⟨742635407, 1474721814⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_227328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 227328 = ⟨93264681, 181465297⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_113664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_228352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 228352 = ⟨1003929718, 1210158129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_228864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 228864 = ⟨263332046, 1021701263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_237056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 237056 = ⟨1403249438, 1011690177⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_244736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 244736 = ⟨1580147207, 1037897828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_245248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 245248 = ⟨1698380406, 1438474911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_253440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 253440 = ⟨857060062, 971778527⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_258048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 258048 = ⟨404074859, 398369746⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_129024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_260096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 260096 = ⟨1507433429, 1550510602⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_130048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_261120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 261120 = ⟨1180041506, 65131525⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_130560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_261632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 261632 = ⟨1370436918, 903797508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_130816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_277504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 277504 = ⟨1284838399, 694370369⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_138752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_292864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 292864 = ⟨1183893609, 1128652358⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_146432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_293888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 293888 = ⟨160947957, 1949876126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_146944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_310272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 310272 = ⟨145249878, 1226307880⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_155136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_323584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 323584 = ⟨655623719, 353143806⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_161792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_325632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 325632 = ⟨1854849082, 2091484047⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_162816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_326656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 326656 = ⟨182991565, 440779355⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_163328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_343040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 343040 = ⟨308930783, 795492293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_171520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_358400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 358400 = ⟨1007493001, 1726918802⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_179200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_359424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 359424 = ⟨1746269657, 798720642⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_179712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_375808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 375808 = ⟨1373792598, 755838059⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_187904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_389120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 389120 = ⟨875099799, 1659345298⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_194560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_391168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 391168 = ⟨298589147, 981397056⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_195584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_392192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 392192 = ⟨260584123, 290605303⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_196096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_408576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 408576 = ⟨678062082, 1146474809⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_204288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_423936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 423936 = ⟨1356662908, 725095927⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_211968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_424960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 424960 = ⟨330798632, 94997784⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_212480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_441344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 441344 = ⟨529328076, 1534660740⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_220672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_454656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 454656 = ⟨1775957340, 1042791219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_227328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_456704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 456704 = ⟨736440378, 211006336⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_228352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_457728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 457728 = ⟨288471726, 1157093446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_228864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_474112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 474112 = ⟨1488136137, 1652345141⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_237056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_489472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 489472 = ⟨1489653516, 1781773511⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_244736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_490496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 490496 = ⟨1469744156, 1311715104⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_245248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_506880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 506880 = ⟨999394676, 1185189761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_253440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_520192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 520192 = ⟨1309629376, 2080668066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_260096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_522240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 522240 = ⟨50276117, 2135200447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_261120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_523264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 523264 = ⟨1443376415, 1022203146⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_261632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_555008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 555008 = ⟨1013914304, 1148447691⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_277504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_585728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 585728 = ⟨1272345615, 2072662117⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_292864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_587776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 587776 = ⟨64474121, 449090084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_293888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_620544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 620544 = ⟨489134626, 1172670349⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_310272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_651264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 651264 = ⟨274337143, 1881376116⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_325632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_653312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 653312 = ⟨1274998107, 355777824⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_326656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_686080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 686080 = ⟨1926375105, 1072595452⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_343040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_716800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 716800 = ⟨401706099, 967129345⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_358400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_718848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 718848 = ⟨1286441580, 875634271⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_359424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_751616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 751616 = ⟨253988194, 1876536006⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_375808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_782336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 782336 = ⟨18011247, 565274326⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_391168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_784384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 784384 = ⟨960504528, 1868249737⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_392192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_817152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 817152 = ⟨1901654770, 162583768⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_408576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_847872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 847872 = ⟨854296756, 1657148963⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_423936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_849920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 849920 = ⟨1889066054, 1080216443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_424960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_882688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 882688 = ⟨294734822, 2050527872⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_441344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_913408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 913408 = ⟨936298450, 1105042578⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_456704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_915456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 915456 = ⟨974728791, 277029768⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_457728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_948224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 948224 = ⟨762862221, 98525728⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_474112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_978944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 978944 = ⟨702523908, 198087577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_489472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_980992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 980992 = ⟨1940083288, 544224765⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_490496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1013760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1013760 = ⟨1049862387, 320373803⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_506880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1044480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1044480 = ⟨1807661853, 544066780⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_522240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1046528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1046528 = ⟨1332596176, 578200921⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_523264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1110016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1110016 = ⟨598225672, 477392696⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_555008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1175552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1175552 = ⟨531874659, 2093948690⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_587776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1241088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1241088 = ⟨463066423, 383444756⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_620544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1306624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1306624 = ⟨931704942, 1582955093⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_653312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1372160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1372160 = ⟨1258493728, 1482265298⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_686080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1437696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1437696 = ⟨1568619121, 824042977⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_718848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1503232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1503232 = ⟨1767305484, 1767768510⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_751616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1568768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1568768 = ⟨1286492231, 1508399759⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_784384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1634304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1634304 = ⟨1788571406, 979662875⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_817152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1699840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1699840 = ⟨1734948438, 924408729⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_849920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1765376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1765376 = ⟨1055629173, 1510653447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_882688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1830912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1830912 = ⟨931164423, 2037669329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_915456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1896448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1896448 = ⟨1287455995, 1262269285⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_948224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1961984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1961984 = ⟨1577684276, 2022021752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_980992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2027520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2027520 = ⟨498379185, 365852161⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1013760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2093056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2093056 = ⟨1942053500, 1814876063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1046528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 480) = ⟨1168068815, 1631133982⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 480 = 61440 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_61440

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1168068815, 1631133982⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 480) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 481) = ⟨598225672, 477392696⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 481 = 1110016 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1110016

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨598225672, 477392696⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 481) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 482) = ⟨1272345615, 2072662117⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 482 = 585728 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_585728

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1272345615, 2072662117⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 482) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 483) = ⟨1788571406, 979662875⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 483 = 1634304 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1634304

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1788571406, 979662875⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 483) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 484) = ⟨655623719, 353143806⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 484 = 323584 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_323584

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨655623719, 353143806⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 484) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 485) = ⟨1258493728, 1482265298⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 485 = 1372160 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1372160

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1258493728, 1482265298⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 485) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 486) = ⟨854296756, 1657148963⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 486 = 847872 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_847872

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨854296756, 1657148963⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 486) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 487) = ⟨1287455995, 1262269285⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 487 = 1896448 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1896448

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1287455995, 1262269285⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 487) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 488) = ⟨1389630114, 73256692⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 488 = 192512 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_192512

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1389630114, 73256692⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 488) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 489) = ⟨463066423, 383444756⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 489 = 1241088 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1241088

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨463066423, 383444756⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 489) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 490) = ⟨401706099, 967129345⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 490 = 716800 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_716800

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨401706099, 967129345⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 490) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 491) = ⟨1055629173, 1510653447⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 491 = 1765376 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1765376

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1055629173, 1510653447⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 491) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 492) = ⟨1775957340, 1042791219⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 492 = 454656 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_454656

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1775957340, 1042791219⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 492) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 493) = ⟨1767305484, 1767768510⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 493 = 1503232 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1503232

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1767305484, 1767768510⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 493) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 494) = ⟨702523908, 198087577⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 494 = 978944 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_978944

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨702523908, 198087577⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 494) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 495) = ⟨498379185, 365852161⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 495 = 2027520 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2027520

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨498379185, 365852161⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 495) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 496) = ⟨1029759507, 977441374⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 496 = 126976 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_126976

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1029759507, 977441374⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 496) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 497) = ⟨531874659, 2093948690⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 497 = 1175552 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1175552

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨531874659, 2093948690⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 497) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 498) = ⟨274337143, 1881376116⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 498 = 651264 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_651264

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨274337143, 1881376116⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 498) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 499) = ⟨1734948438, 924408729⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 499 = 1699840 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1699840

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1734948438, 924408729⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 499) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 500) = ⟨875099799, 1659345298⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 500 = 389120 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_389120

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨875099799, 1659345298⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 500) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 501) = ⟨1568619121, 824042977⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 501 = 1437696 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1437696

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1568619121, 824042977⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 501) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 502) = ⟨936298450, 1105042578⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 502 = 913408 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_913408

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨936298450, 1105042578⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 502) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 503) = ⟨1577684276, 2022021752⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 503 = 1961984 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1961984

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1577684276, 2022021752⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 503) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 504) = ⟨404074859, 398369746⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 504 = 258048 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_258048

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨404074859, 398369746⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 504) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 505) = ⟨931704942, 1582955093⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 505 = 1306624 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1306624

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨931704942, 1582955093⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 505) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 506) = ⟨18011247, 565274326⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 506 = 782336 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_782336

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨18011247, 565274326⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 506) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 507) = ⟨931164423, 2037669329⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 507 = 1830912 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1830912

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨931164423, 2037669329⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 507) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 508) = ⟨1309629376, 2080668066⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 508 = 520192 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_520192

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1309629376, 2080668066⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 508) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 509) = ⟨1286492231, 1508399759⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 509 = 1568768 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1568768

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1286492231, 1508399759⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 509) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 510) = ⟨1807661853, 544066780⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 510 = 1044480 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1044480

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1807661853, 544066780⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 510) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 511) = ⟨1942053500, 1814876063⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 511 = 2093056 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2093056

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1942053500, 1814876063⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 511) := by
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

end R17TableBChunk15Certificate
