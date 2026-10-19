import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk15Certificate
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

theorem power_30721 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30721 = ⟨404520597, 1583624884⟩ := by
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

theorem power_61442 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61442 = ⟨1198747920, 2105265938⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30721]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63360 = ⟨1322171884, 737849280⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63489 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63489 = ⟨1205004494, 664508590⟩ := by
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

theorem power_96257 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96257 = ⟨2122892738, 382214671⟩ := by
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

theorem power_122884 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122884 = ⟨476263702, 244021279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61442]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126720 = ⟨1786195431, 1289560474⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126978 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126978 = ⟨1677113115, 1896889353⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63489]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_129025 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 129025 = ⟨645645839, 872547302⟩ := by
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

theorem power_161793 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 161793 = ⟨1376140908, 349620710⟩ := by
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

theorem power_192514 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 192514 = ⟨1475607807, 750348151⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96257]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_194561 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 194561 = ⟨1306486153, 1854133037⟩ := by
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

theorem power_227329 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 227329 = ⟨1450657594, 984773671⟩ := by
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

theorem power_245768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 245768 = ⟨1621337090, 1982008239⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122884]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_253440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 253440 = ⟨857060062, 971778527⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_253956 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 253956 = ⟨903493439, 388398758⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126978]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_258050 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 258050 = ⟨1450071122, 1552811030⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_129025]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_260097 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 260097 = ⟨534201605, 2021727871⟩ := by
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

theorem power_292865 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 292865 = ⟨1644964666, 897133957⟩ := by
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

theorem power_323586 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 323586 = ⟨1102117808, 142802229⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_161793]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_325633 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 325633 = ⟨1192178714, 1856692559⟩ := by
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

theorem power_358401 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 358401 = ⟨400120814, 388553978⟩ := by
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

theorem power_385028 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 385028 = ⟨690030080, 678359161⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_192514]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_389122 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 389122 = ⟨1286037179, 1318577381⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_194561]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_391169 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 391169 = ⟨528585109, 882717337⟩ := by
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

theorem power_423937 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 423937 = ⟨1509818833, 1144268234⟩ := by
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

theorem power_454658 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 454658 = ⟨2085347328, 349795556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_227329]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_456705 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 456705 = ⟨1477234131, 1884370798⟩ := by
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

theorem power_489473 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 489473 = ⟨1605929941, 613039796⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_244736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_490496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 490496 = ⟨1469744156, 1311715104⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_245248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_491536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 491536 = ⟨422162039, 314640451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_245768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_506880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 506880 = ⟨999394676, 1185189761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_253440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_507912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 507912 = ⟨532715146, 1905293744⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_253956]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_516100 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 516100 = ⟨1228215638, 1167028638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_258050]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_520194 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 520194 = ⟨2111488801, 113345907⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_260097]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_522241 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 522241 = ⟨1447151645, 100014905⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_261120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_523264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 523264 = ⟨1443376415, 1022203146⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_261632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_555009 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 555009 = ⟨1599855501, 27861569⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_277504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_585730 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 585730 = ⟨263084282, 1519847118⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_292865]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_587777 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 587777 = ⟨1234756902, 2076666495⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_293888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_620545 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 620545 = ⟨611261987, 1609064037⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_310272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_647172 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 647172 = ⟨374512297, 742304187⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_323586]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_651266 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 651266 = ⟨1915937917, 442480677⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_325633]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_653313 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 653313 = ⟨1459112003, 1403452974⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_326656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_686081 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 686081 = ⟨893773507, 1835197624⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_343040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_716802 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 716802 = ⟨98647758, 831124499⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_358401]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_718849 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 718849 = ⟨348156390, 399914027⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_359424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_751617 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 751617 = ⟨74409980, 698970197⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_375808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_770056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 770056 = ⟨850813113, 242457356⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_385028]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_778244 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 778244 = ⟨1642000352, 1458076428⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_389122]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_782338 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 782338 = ⟨1365953737, 2020008228⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_391169]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_784385 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 784385 = ⟨819043667, 1590965510⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_392192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_817153 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 817153 = ⟨1805644484, 1448095994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_408576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_847874 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 847874 = ⟨1476984429, 372276551⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_423937]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_849921 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 849921 = ⟨888470699, 1496630477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_424960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_882689 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 882689 = ⟨1628793757, 386999327⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_441344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_909316 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 909316 = ⟨2036751860, 312805960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_454658]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_913410 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 913410 = ⟨2074767461, 628994045⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_456705]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_915457 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 915457 = ⟨2067383688, 1598427663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_457728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_948225 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 948225 = ⟨1009098657, 764432615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_474112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_978946 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 978946 = ⟨1481372087, 1602904549⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_489473]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_980993 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 980993 = ⟨683695561, 381076576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_490496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_983072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 983072 = ⟨938254867, 428236877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_491536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1013761 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1013761 = ⟨2074775246, 1659462046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_506880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1015824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1015824 = ⟨919394853, 515189054⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_507912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1032200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1032200 = ⟨444839547, 1006735803⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_516100]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1040388 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1040388 = ⟨1029442175, 844540434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_520194]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1044482 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1044482 = ⟨1653584892, 189141014⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_522241]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1046529 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1046529 = ⟨346681555, 251061519⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_523264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1110018 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1110018 = ⟨2133217011, 1335517857⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_555009]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1171460 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1171460 = ⟨1096891632, 1038162044⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_585730]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1175554 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1175554 = ⟨18627402, 1994522105⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_587777]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1241090 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1241090 = ⟨277492837, 702067940⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_620545]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1294344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1294344 = ⟨53525523, 1043053171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_647172]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1302532 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1302532 = ⟨223035528, 1392456980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_651266]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1306626 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1306626 = ⟨714770550, 187684655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_653313]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1372162 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1372162 = ⟨312083357, 769683136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_686081]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1433604 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1433604 = ⟨59975189, 1479615296⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_716802]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1437698 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1437698 = ⟨2115256098, 1865306265⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_718849]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1503234 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1503234 = ⟨1842884363, 1922214380⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_751617]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1540112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1540112 = ⟨123570745, 1206032145⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_770056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1556488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1556488 = ⟨1748162482, 844026790⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_778244]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1564676 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1564676 = ⟨1075639351, 1532627745⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_782338]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1568770 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1568770 = ⟨1772547158, 1657109441⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_784385]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1634306 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1634306 = ⟨1348120477, 722825044⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_817153]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1695748 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1695748 = ⟨544321985, 1624857853⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_847874]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1699842 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1699842 = ⟨1518598353, 1217059617⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_849921]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1765378 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1765378 = ⟨826421745, 759950126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_882689]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1818632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1818632 = ⟨941496351, 1490141975⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_909316]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1826820 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1826820 = ⟨2045638044, 832545679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_913410]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1830914 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1830914 = ⟨1798796265, 1046278428⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_915457]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1896450 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1896450 = ⟨950888429, 1771882874⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_948225]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1957892 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1957892 = ⟨616125559, 1948697858⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_978946]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1961986 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1961986 = ⟨1504315151, 337944338⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_980993]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1966144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1966144 = ⟨2015771726, 370776663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_983072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2027522 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2027522 = ⟨1232582392, 1356628612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1013761]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2031648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2031648 = ⟨815944321, 1740024022⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1015824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2064400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2064400 = ⟨182866310, 519442228⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1032200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2080776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2080776 = ⟨1581272673, 947463371⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1040388]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2088964 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2088964 = ⟨468589054, 241109042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1044482]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2093058 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2093058 = ⟨686855572, 1662818962⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1046529]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2220036 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2220036 = ⟨1100354965, 1461934907⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1110018]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2342920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2342920 = ⟨2072828291, 1320593778⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1171460]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2351108 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2351108 = ⟨870011157, 1748996844⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1175554]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2482180 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2482180 = ⟨1400939605, 521922217⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1241090]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2588688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2588688 = ⟨113281423, 344979790⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1294344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2605064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2605064 = ⟨1655405361, 2091373257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1302532]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2613252 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2613252 = ⟨2043114755, 2092611458⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1306626]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2744324 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2744324 = ⟨1598697786, 1412816199⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1372162]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2867208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2867208 = ⟨2143525205, 250862462⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1433604]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2875396 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2875396 = ⟨1109606406, 1659310456⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1437698]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3006468 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3006468 = ⟨1324437357, 769920740⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1503234]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3080224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3080224 = ⟨753926228, 107311772⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1540112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3112976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3112976 = ⟨1479431406, 1004484072⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1556488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3129352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3129352 = ⟨1782299944, 815992650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1564676]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3137540 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3137540 = ⟨2044118175, 1815386539⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1568770]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3268612 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3268612 = ⟨177947674, 598162574⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1634306]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3391496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3391496 = ⟨1611621051, 583453374⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1695748]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3399684 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3399684 = ⟨393965872, 1504220744⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1699842]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3530756 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3530756 = ⟨1039002289, 1535992398⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1765378]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3637264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3637264 = ⟨608722910, 1856429587⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1818632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3653640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3653640 = ⟨893594521, 1827626780⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1826820]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3661828 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3661828 = ⟨1154478017, 1884256484⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1830914]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3792900 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3792900 = ⟨1396076166, 1121488767⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1896450]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3915784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3915784 = ⟨1691039315, 2094964745⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1957892]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3923972 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3923972 = ⟨433736985, 1092489424⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1961986]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3932288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3932288 = ⟨206096517, 54790766⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1966144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4055044 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4055044 = ⟨1862343123, 811292110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2027522]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4063296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4063296 = ⟨1890247028, 1206340187⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2031648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4128800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4128800 = ⟨525818523, 99397767⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2064400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4161552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4161552 = ⟨332114012, 1793344046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2080776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4177928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4177928 = ⟨1644661702, 1667995113⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2088964]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4186116 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4186116 = ⟨872119931, 371662931⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2093058]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4440072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4440072 = ⟨806473021, 1955602838⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2220036]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4685840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4685840 = ⟨1924221980, 853079915⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2342920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4702216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4702216 = ⟨222105658, 296180074⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2351108]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4964360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4964360 = ⟨636269889, 1336306443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2482180]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5177376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5177376 = ⟨696981702, 819551393⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2588688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5210128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5210128 = ⟨1033581439, 964743696⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2605064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5226504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5226504 = ⟨1409555490, 898555037⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2613252]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5488648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5488648 = ⟨601823854, 1670055343⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2744324]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5734416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5734416 = ⟨297274056, 1847195661⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2867208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5750792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5750792 = ⟨396806078, 949327090⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2875396]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6012936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6012936 = ⟨18655302, 122183690⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3006468]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6160448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6160448 = ⟨445496213, 999354785⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3080224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6225952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6225952 = ⟨2095687072, 4636002⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3112976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6258704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6258704 = ⟨1757300439, 476021381⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3129352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6275080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6275080 = ⟨631414193, 1384597826⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3137540]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6537224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6537224 = ⟨620077885, 134241605⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3268612]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6782992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6782992 = ⟨2725142, 2015114734⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3391496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6799368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6799368 = ⟨888437105, 1845063571⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3399684]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7061512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7061512 = ⟨900798612, 440115417⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3530756]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7274528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7274528 = ⟨371115705, 1134969176⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3637264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7307280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7307280 = ⟨324602262, 1533257480⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3653640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7323656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7323656 = ⟨256663570, 1426544129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3661828]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7585800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7585800 = ⟨1420835134, 1350897974⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3792900]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7831568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7831568 = ⟨890227922, 2127423494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3915784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7847944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7847944 = ⟨436833722, 713704460⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3923972]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7864576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7864576 = ⟨1109116968, 1669279495⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3932288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8110088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8110088 = ⟨554277227, 818735958⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4055044]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8126592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8126592 = ⟨798103159, 432019009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4063296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8257600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8257600 = ⟨238013106, 1231383326⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4128800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8323104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8323104 = ⟨929117735, 1425005032⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4161552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8355856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8355856 = ⟨678451002, 1312645343⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4177928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8372232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8372232 = ⟨899107850, 1412103870⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4186116]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8880144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8880144 = ⟨828652000, 1878180546⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4440072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9371680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9371680 = ⟨1480249453, 997391523⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4685840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9404432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9404432 = ⟨1142137633, 1328323116⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4702216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9928720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9928720 = ⟨181604879, 2136651446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4964360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10354752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10354752 = ⟨1170921556, 438625121⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5177376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10420256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10420256 = ⟨328795273, 406652505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5210128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10453008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10453008 = ⟨1452913444, 762045371⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5226504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10977296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10977296 = ⟨1490558251, 1095595779⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5488648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11468832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11468832 = ⟨617631607, 2065701736⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5734416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11501584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11501584 = ⟨490697782, 1180338514⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5750792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12025872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12025872 = ⟨333240414, 267520456⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6012936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12320896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12320896 = ⟨1781427130, 264980350⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6160448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12451904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12451904 = ⟨1151073992, 897261486⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6225952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12517408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12517408 = ⟨15281426, 1604945521⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6258704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12550160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12550160 = ⟨1416547397, 184428904⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6275080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13074448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13074448 = ⟨453607293, 966998822⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6537224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13565984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13565984 = ⟨800937675, 1110072005⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6782992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13598736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13598736 = ⟨1842934519, 618936341⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6799368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14123024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14123024 = ⟨991127008, 1596891927⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7061512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14549056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14549056 = ⟨2061671116, 2069905314⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7274528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14614560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14614560 = ⟨1663639894, 162989883⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7307280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14647312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14647312 = ⟨421735092, 947128485⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7323656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15171600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15171600 = ⟨1412026757, 1189789363⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7585800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15663136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15663136 = ⟨1559553961, 1232079888⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7831568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15695888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15695888 = ⟨632068827, 1778818746⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7847944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15729152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15729152 = ⟨774268257, 1064958851⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7864576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16220176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16220176 = ⟨133958936, 232161545⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8110088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16253184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16253184 = ⟨1254438166, 1202697218⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8126592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16515200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16515200 = ⟨249025509, 1264405525⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8257600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16646208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16646208 = ⟨1576049820, 743532376⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8323104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16711712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16711712 = ⟨981345409, 1345792419⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8355856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16744464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16744464 = ⟨161733731, 289098559⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8372232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17760288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17760288 = ⟨776543635, 1166304553⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8880144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18743360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18743360 = ⟨265064458, 1447346174⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9371680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18808864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18808864 = ⟨370922798, 1284732467⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9404432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19857440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19857440 = ⟨1708451712, 736178402⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9928720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20709504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20709504 = ⟨316120189, 595560857⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10354752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20840512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20840512 = ⟨162360108, 760325311⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10420256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20906016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20906016 = ⟨301284527, 1036754347⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10453008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21954592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21954592 = ⟨320517229, 1018408923⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10977296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22937664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22937664 = ⟨2034389515, 1486256980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11468832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23003168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23003168 = ⟨1409791745, 86443440⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11501584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24051744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24051744 = ⟨520593297, 720605105⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12025872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24641792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24641792 = ⟨142863564, 77814322⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12320896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24903808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24903808 = ⟨1359999522, 1766323361⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12451904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25034816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25034816 = ⟨627702803, 1210657391⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12517408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25100320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25100320 = ⟨1542958391, 1658892373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12550160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26148896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26148896 = ⟨872057611, 52224469⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13074448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27131968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27131968 = ⟨1106399632, 1919232485⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13565984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27197472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27197472 = ⟨928624551, 1865263700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13598736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28246048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28246048 = ⟨1176293813, 93545973⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14123024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29098112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29098112 = ⟨663172513, 484483528⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14549056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29229120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29229120 = ⟨90827609, 952725283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14614560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29294624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29294624 = ⟨1116645838, 592225416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14647312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30343200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30343200 = ⟨248954754, 1709366485⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15171600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31326272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31326272 = ⟨1318624849, 350151544⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15663136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31391776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31391776 = ⟨437637952, 715464789⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15695888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31458304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31458304 = ⟨1529521733, 1200601350⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15729152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32440352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32440352 = ⟨819324931, 1791299901⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16220176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32506368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32506368 = ⟨1159112245, 428855495⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16253184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33030400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33030400 = ⟨1334041147, 1226132263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16515200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33292416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33292416 = ⟨1115672029, 792075042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16646208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33423424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33423424 = ⟨97955019, 2098325084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16711712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33488928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33488928 = ⟨890000918, 192425⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16744464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35520576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35520576 = ⟨200979164, 1956645614⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17760288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37486720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37486720 = ⟨501019171, 1803065891⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18743360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37617728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37617728 = ⟨706107185, 887445053⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18808864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39714880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39714880 = ⟨481771245, 1468667855⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19857440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41419008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41419008 = ⟨550062200, 1202736475⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20709504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41681024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41681024 = ⟨1042430763, 1925747559⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20840512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41812032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41812032 = ⟨1807414066, 2129565626⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20906016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43909184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43909184 = ⟨743363350, 753558739⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21954592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45875328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45875328 = ⟨28124134, 723040035⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22937664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46006336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46006336 = ⟨1209343314, 718504407⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23003168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48103488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48103488 = ⟨97665982, 48741334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24051744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49283584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49283584 = ⟨1757646914, 40757884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24641792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49807616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49807616 = ⟨2024602086, 332704654⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24903808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50069632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50069632 = ⟨292949450, 1357127875⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25034816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50200640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50200640 = ⟨584242869, 1794820100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25100320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52297792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52297792 = ⟨674826074, 373549529⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26148896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54263936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54263936 = ⟨543993125, 723905149⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27131968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54394944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54394944 = ⟨1764106614, 1661082780⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27197472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56492096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56492096 = ⟨1536240551, 1587278007⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28246048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58196224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58196224 = ⟨1786643843, 2018390573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29098112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58458240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58458240 = ⟨1127368178, 1537032273⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29229120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58589248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58589248 = ⟨1468710851, 1277826113⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29294624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60686400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60686400 = ⟨1822900322, 396992021⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30343200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62652544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62652544 = ⟨1555405080, 771062823⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31326272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62783552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62783552 = ⟨944169748, 691005588⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31391776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64880704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64880704 = ⟨868910853, 282566473⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32440352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65012736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65012736 = ⟨1755212887, 1545248590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32506368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66060800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66060800 = ⟨1537189271, 1250290056⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33030400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66584832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66584832 = ⟨2059139424, 1336500201⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33292416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66846848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66846848 = ⟨210971910, 757588334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33423424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66977856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66977856 = ⟨1107166396, 1801530388⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33488928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71041152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71041152 = ⟨2005622177, 1693587977⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35520576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_74973440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 74973440 = ⟨206280645, 1924267158⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37486720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_75235456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 75235456 = ⟨2011826429, 430797016⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37617728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_79429760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79429760 = ⟨1232974476, 1920034974⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39714880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_82838016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 82838016 = ⟨1387475458, 1047220957⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41419008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_83362048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83362048 = ⟨1854150499, 2115940882⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41681024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_83624064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83624064 = ⟨1689725648, 1429212690⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41812032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87818368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87818368 = ⟨1570197274, 841588068⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43909184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_91750656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 91750656 = ⟨735355596, 2129370811⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45875328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92012672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92012672 = ⟨919528823, 1215035091⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46006336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_96206976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96206976 = ⟨1137807209, 598244296⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48103488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98567168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98567168 = ⟨388664435, 1700426073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49283584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_99615232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 99615232 = ⟨629993962, 605215182⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49807616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_100139264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100139264 = ⟨447731677, 53301370⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50069632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_100401280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100401280 = ⟨620819109, 2110467503⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50200640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104595584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104595584 = ⟨1708888904, 1596625862⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52297792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108527872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108527872 = ⟨689140832, 1731654679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54263936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108789888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108789888 = ⟨730888523, 1783434181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54394944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_112984192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112984192 = ⟨1816210254, 586931420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56492096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_116392448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116392448 = ⟨56044666, 511148921⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58196224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_116916480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116916480 = ⟨1775639415, 1607326067⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58458240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_117178496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117178496 = ⟨662668089, 1050028928⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58589248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121372800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121372800 = ⟨948992359, 209295678⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60686400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125305088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125305088 = ⟨893878252, 1713844219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62652544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125567104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125567104 = ⟨573918982, 2065324330⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62783552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_129761408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 129761408 = ⟨1545458758, 356537823⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64880704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_132121600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 132121600 = ⟨1887931203, 983768063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66060800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_133169664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 133169664 = ⟨1974900439, 113641696⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66584832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_133693696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 133693696 = ⟨471251868, 1616023242⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66846848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_133955712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 133955712 = ⟨2119745010, 1317158845⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66977856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_142082304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 142082304 = ⟨1500787244, 1069761338⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71041152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_149946880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 149946880 = ⟨19705188, 601131721⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74973440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_150470912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 150470912 = ⟨710360401, 1658515073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75235456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_158859520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 158859520 = ⟨920760142, 725370091⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79429760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_165676032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 165676032 = ⟨1811854824, 734127761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82838016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_166724096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 166724096 = ⟨659358103, 68552034⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83362048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_167248128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 167248128 = ⟨395330563, 1719642529⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83624064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_175636736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 175636736 = ⟨588726501, 2095759668⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87818368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_183501312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 183501312 = ⟨1087513177, 185443333⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91750656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_184025344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 184025344 = ⟨1230240434, 2039360919⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92012672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_192413952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 192413952 = ⟨661546131, 1826102720⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96206976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_199230464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 199230464 = ⟨1461518819, 1258709018⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99615232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_200278528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 200278528 = ⟨2138483735, 1770586612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100139264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_200802560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 200802560 = ⟨1163777347, 688067308⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100401280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_209191168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 209191168 = ⟨1710457520, 367146312⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104595584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_217055744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 217055744 = ⟨279657220, 303332766⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108527872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_217579776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 217579776 = ⟨1566007568, 1379981863⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108789888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_225968384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 225968384 = ⟨1627048971, 1888559675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112984192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_232784896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 232784896 = ⟨1031337775, 1391460640⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116392448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_233832960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 233832960 = ⟨1188165896, 2112922903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116916480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_234356992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 234356992 = ⟨1073949532, 1594135507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117178496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_242745600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 242745600 = ⟨1826826616, 226261821⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121372800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_250610176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 250610176 = ⟨100843231, 438309932⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125305088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_251134208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 251134208 = ⟨1678391460, 1567925032⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125567104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_259522816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 259522816 = ⟨878040696, 142913800⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_129761408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_266339328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 266339328 = ⟨162197904, 1576977305⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133169664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_267387392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 267387392 = ⟨1559132762, 1714911077⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133693696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_267911424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 267911424 = ⟨806115454, 961207530⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133955712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_284164608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 284164608 = ⟨812805536, 1259409747⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_142082304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_299893760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 299893760 = ⟨799417018, 157314149⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_149946880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_300941824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 300941824 = ⟨998137510, 357094521⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_150470912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_317719040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 317719040 = ⟨1029663537, 756849066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_158859520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_333448192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 333448192 = ⟨97731769, 427520892⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_166724096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_334496256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 334496256 = ⟨1200629285, 569929446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_167248128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_351273472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 351273472 = ⟨1114640670, 275606456⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_175636736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_367002624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 367002624 = ⟨2129034372, 1920159279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_183501312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_368050688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 368050688 = ⟨1708935583, 1945239173⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_184025344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_384827904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 384827904 = ⟨1475977678, 729783072⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_192413952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_400557056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 400557056 = ⟨1403104042, 1214106139⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_200278528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_401605120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 401605120 = ⟨1339817084, 956567823⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_200802560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_418382336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 418382336 = ⟨471246081, 1857200807⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_209191168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_434111488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 434111488 = ⟨1312626624, 408174531⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_217055744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_435159552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 435159552 = ⟨58501987, 31808713⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_217579776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_451936768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 451936768 = ⟨1664043999, 1087752763⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_225968384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_467665920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 467665920 = ⟨822026787, 790328297⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_233832960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_468713984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 468713984 = ⟨1460037887, 720267794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_234356992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_485491200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 485491200 = ⟨1548821183, 558694761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_242745600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_501220352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 501220352 = ⟨2083000424, 83400055⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_250610176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_502268416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 502268416 = ⟨1326466242, 1443346206⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_251134208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_519045632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 519045632 = ⟨1770364962, 715559965⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_259522816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_534774784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 534774784 = ⟨1519708073, 1761924179⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_267387392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_535822848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 535822848 = ⟨2027963173, 2122680648⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_267911424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_568329216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 568329216 = ⟨1200601350, 617961914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_284164608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_601883648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 601883648 = ⟨1545248590, 392270760⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_300941824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_635438080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 635438080 = ⟨1700426073, 1758819212⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_317719040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_668992512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 668992512 = ⟨983768063, 259552444⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_334496256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_702546944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 702546944 = ⟨734127761, 335628823⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_351273472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_736101376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 736101376 = ⟨1258709018, 685964828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_368050688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_769655808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 769655808 = ⟨1391460640, 1116145872⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_384827904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_803210240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 803210240 = ⟨1576977305, 1985285743⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_401605120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_836764672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 836764672 = ⟨157314149, 1348066629⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_418382336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_870319104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 870319104 = ⟨427520892, 2049751878⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_435159552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_903873536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 903873536 = ⟨1920159279, 18449275⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_451936768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_937427968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 937427968 = ⟨1214106139, 744379605⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_468713984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_970982400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 970982400 = ⟨408174531, 834857023⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_485491200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1004536832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1004536832 = ⟨790328297, 1325456860⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_502268416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1038091264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1038091264 = ⟨83400055, 64483223⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_519045632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1071645696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1071645696 = ⟨1761924179, 627775574⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_535822848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 480) = ⟨1529521733, 1200601350⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 480 = 31458304 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_31458304

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1529521733, 1200601350⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 480) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 481) = ⟨1200601350, 617961914⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 481 = 568329216 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_568329216

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1200601350, 617961914⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 481) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 482) = ⟨799417018, 157314149⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 482 = 299893760 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_299893760

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨799417018, 157314149⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 482) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 483) = ⟨157314149, 1348066629⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 483 = 836764672 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_836764672

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨157314149, 1348066629⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 483) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 484) = ⟨1811854824, 734127761⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 484 = 165676032 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_165676032

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1811854824, 734127761⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 484) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 485) = ⟨734127761, 335628823⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 485 = 702546944 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_702546944

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨734127761, 335628823⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 485) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 486) = ⟨1312626624, 408174531⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 486 = 434111488 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_434111488

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1312626624, 408174531⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 486) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 487) = ⟨408174531, 834857023⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 487 = 970982400 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_970982400

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨408174531, 834857023⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 487) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 488) = ⟨388664435, 1700426073⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 488 = 98567168 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_98567168

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨388664435, 1700426073⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 488) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 489) = ⟨1700426073, 1758819212⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 489 = 635438080 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_635438080

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1700426073, 1758819212⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 489) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 490) = ⟨2129034372, 1920159279⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 490 = 367002624 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_367002624

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2129034372, 1920159279⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 490) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 491) = ⟨1920159279, 18449275⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 491 = 903873536 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_903873536

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1920159279, 18449275⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 491) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 492) = ⟨1031337775, 1391460640⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 492 = 232784896 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_232784896

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1031337775, 1391460640⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 492) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 493) = ⟨1391460640, 1116145872⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 493 = 769655808 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_769655808

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1391460640, 1116145872⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 493) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 494) = ⟨2083000424, 83400055⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 494 = 501220352 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_501220352

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2083000424, 83400055⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 494) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 495) = ⟨83400055, 64483223⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 495 = 1038091264 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1038091264

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨83400055, 64483223⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 495) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 496) = ⟨1755212887, 1545248590⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 496 = 65012736 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_65012736

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1755212887, 1545248590⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 496) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 497) = ⟨1545248590, 392270760⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 497 = 601883648 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_601883648

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1545248590, 392270760⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 497) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 498) = ⟨97731769, 427520892⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 498 = 333448192 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_333448192

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨97731769, 427520892⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 498) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 499) = ⟨427520892, 2049751878⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 499 = 870319104 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_870319104

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨427520892, 2049751878⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 499) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 500) = ⟨1461518819, 1258709018⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 500 = 199230464 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_199230464

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1461518819, 1258709018⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 500) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 501) = ⟨1258709018, 685964828⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 501 = 736101376 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_736101376

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1258709018, 685964828⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 501) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 502) = ⟨822026787, 790328297⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 502 = 467665920 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_467665920

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨822026787, 790328297⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 502) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 503) = ⟨790328297, 1325456860⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 503 = 1004536832 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1004536832

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨790328297, 1325456860⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 503) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 504) = ⟨1887931203, 983768063⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 504 = 132121600 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_132121600

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1887931203, 983768063⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 504) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 505) = ⟨983768063, 259552444⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 505 = 668992512 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_668992512

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨983768063, 259552444⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 505) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 506) = ⟨1403104042, 1214106139⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 506 = 400557056 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_400557056

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1403104042, 1214106139⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 506) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 507) = ⟨1214106139, 744379605⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 507 = 937427968 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_937427968

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1214106139, 744379605⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 507) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 508) = ⟨162197904, 1576977305⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 508 = 266339328 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_266339328

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨162197904, 1576977305⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 508) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 509) = ⟨1576977305, 1985285743⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 509 = 803210240 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_803210240

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1576977305, 1985285743⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 509) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 510) = ⟨1519708073, 1761924179⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 510 = 534774784 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_534774784

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1519708073, 1761924179⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 510) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 511) = ⟨1761924179, 627775574⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 511 = 1071645696 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1071645696

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1761924179, 627775574⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 511) := by
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

end R17TableAChunk15Certificate
