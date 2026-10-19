import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk07Certificate
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

theorem power_56 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56 = ⟨1662653600, 373479491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28]
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

theorem power_112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112 = ⟨2110227055, 661472412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56]
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

theorem power_142 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 142 = ⟨2045471800, 21567742⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71]
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

theorem power_156 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 156 = ⟨58128200, 444904138⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78]
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

theorem power_174 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 174 = ⟨1566056996, 1745888105⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87]
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

theorem power_184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 184 = ⟨337081033, 972978617⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92]
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

theorem power_206 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 206 = ⟨891793723, 1417325858⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103]
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

theorem power_220 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 220 = ⟨103472470, 1652631780⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110]
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

theorem power_224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 224 = ⟨1497340852, 2054439268⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_231 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 231 = ⟨235212131, 119569981⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_238 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 238 = ⟨1707325511, 1098406816⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119]
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

theorem power_270 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 270 = ⟨529601202, 621421182⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_135]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_284 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 284 = ⟨23079860, 1037577460⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_142]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_286 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 286 = ⟨1312976075, 1874233770⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_143]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_302 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 302 = ⟨2109094984, 117233691⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_151]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 312 = ⟨715656401, 189653281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_156]
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

theorem power_334 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 334 = ⟨753378315, 1427449060⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_167]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_348 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 348 = ⟨1388299958, 1206426289⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_174]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_350 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 350 = ⟨2091438009, 37173329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_175]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_366 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 366 = ⟨1117728476, 862089260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_183]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 368 = ⟨2105144309, 259436035⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_184]
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

theorem power_398 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 398 = ⟨1915229291, 1105504804⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_199]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_412 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 412 = ⟨2105482584, 779799999⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_206]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_414 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 414 = ⟨2113912359, 1823140805⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_207]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_430 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 430 = ⟨263286599, 1282534279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_215]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 440 = ⟨1338202108, 1403991666⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_220]
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

theorem power_448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 448 = ⟨1326191972, 1554410474⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_462 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 462 = ⟨942972626, 1810202834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_231]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_476 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 476 = ⟨795892619, 307427987⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_238]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_478 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 478 = ⟨1458859561, 318476705⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_239]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 480 = ⟨300788412, 2003762236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_494 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 494 = ⟨1055176129, 673017746⟩ := by
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

theorem power_540 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 540 = ⟨630512252, 401771957⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_270]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 568 = ⟨1827897087, 929922642⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_284]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_572 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 572 = ⟨1434583057, 1273507208⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_286]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_604 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 604 = ⟨538020577, 631501536⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_302]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 624 = ⟨1784074070, 421362258⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_312]
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

theorem power_668 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 668 = ⟨426899686, 373278555⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_334]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 696 = ⟨1453440674, 589119313⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_348]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_700 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 700 = ⟨2039040404, 1736652883⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_350]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_732 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 732 = ⟨554792626, 1839590779⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_366]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 736 = ⟨103504458, 1923745518⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_368]
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

theorem power_796 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 796 = ⟨700492617, 8678681⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_398]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 824 = ⟨393192345, 1269883945⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_412]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_828 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 828 = ⟨1643040924, 1014125157⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_414]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_860 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 860 = ⟨1223844726, 1188846095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_430]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 880 = ⟨1135809938, 233595019⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_440]
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

theorem power_896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 896 = ⟨1475671350, 739745329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_924 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 924 = ⟨1091307962, 1671174009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_462]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 952 = ⟨736233126, 745912594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_476]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_956 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 956 = ⟨1766003384, 644713738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_478]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 960 = ⟨418523497, 1921984699⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_988 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 988 = ⟨930302072, 933399811⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_494]
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

theorem power_1080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1080 = ⟨2042646259, 94992365⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_540]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1136 = ⟨934113032, 310511167⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1144 = ⟨684087935, 140548154⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_572]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1208 = ⟨176440113, 1084668010⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_604]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1248 = ⟨202925653, 1282518697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_624]
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

theorem power_1336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1336 = ⟨1009955505, 1510543494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_668]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1392 = ⟨1354106400, 443181508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1400 = ⟨1642577879, 155228252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_700]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1464 = ⟨1315909298, 1789467885⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_732]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1472 = ⟨1509980434, 1580004926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_736]
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

theorem power_1592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1592 = ⟨527586588, 1562116815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_796]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1648 = ⟨319382324, 289573192⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1656 = ⟨502735259, 193158691⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_828]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1720 = ⟨1990060689, 1173021817⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_860]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1760 = ⟨2006415565, 2089899884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_880]
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

theorem power_1792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1792 = ⟨344093444, 1723950257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1848 = ⟨2109320268, 1124983315⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_924]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1904 = ⟨547307125, 463271940⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1912 = ⟨679289911, 1807755185⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_956]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1920 = ⟨203869561, 313423390⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1976 = ⟨816997558, 1117506323⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_988]
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

theorem power_2160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2160 = ⟨1565483443, 2098430477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2272 = ⟨308268370, 2093673186⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2288 = ⟨853372384, 1508779871⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2416 = ⟨1645200661, 71941409⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2496 = ⟨603512862, 13573590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1248]
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

theorem power_2672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2672 = ⟨1012691958, 881525569⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2784 = ⟨1360272642, 462407257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2800 = ⟨2102317524, 705206869⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2928 = ⟨1575004799, 500091894⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2944 = ⟨1091919627, 1535715623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1472]
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

theorem power_3184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3184 = ⟨1911211217, 1209662043⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3296 = ⟨903616870, 1432862237⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3312 = ⟨84826221, 1783037972⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3440 = ⟨1298571999, 1740873419⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3520 = ⟨19290124, 887640976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1760]
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

theorem power_3584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3584 = ⟨1309393381, 53742718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3696 = ⟨1519898835, 1228368252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3808 = ⟨1506184608, 1755829396⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3824 = ⟨1061710231, 784310051⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3840 = ⟨2080156404, 1988869649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3952 = ⟨242936601, 625351024⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1976]
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

theorem power_4320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4320 = ⟨126966968, 506934318⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4544 = ⟨609701741, 767315046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4576 = ⟨1883111880, 197853127⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4832 = ⟨513734373, 631097729⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4992 = ⟨2028012531, 2010507233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2496]
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

theorem power_5344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5344 = ⟨1939587010, 1616699649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5568 = ⟨99211207, 1946280920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5600 = ⟨397407191, 173471874⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5856 = ⟨894294574, 273299880⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5888 = ⟨1683866914, 365976087⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2944]
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

theorem power_6368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6368 = ⟨428722550, 108559190⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6592 = ⟨2029889606, 1568983310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6624 = ⟨424967641, 588853096⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6880 = ⟨205625603, 17388685⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7040 = ⟨867551960, 518924681⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3520]
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

theorem power_7168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7168 = ⟨1883166840, 347102028⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7392 = ⟨1052737347, 1152187489⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7616 = ⟨1101130210, 28496752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7648 = ⟨59592689, 1115813540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7680 = ⟨1699022782, 2146531477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7904 = ⟨1388086223, 26444797⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3952]
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

theorem power_8640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8640 = ⟨1961795311, 1082834093⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9088 = ⟨236427592, 1624003215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9152 = ⟨2124389071, 474079624⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9664 = ⟨1211655166, 348770789⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9984 = ⟨1723471681, 1868423509⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4992]
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

theorem power_10688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10688 = ⟨1911771696, 801892733⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11136 = ⟨147298690, 1099763101⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11200 = ⟨1563170848, 460055775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11712 = ⟨933367959, 293609717⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11776 = ⟨1650999925, 82499284⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5888]
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

theorem power_12736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12736 = ⟨927007817, 1410344259⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13184 = ⟨917179047, 586675057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13248 = ⟨1989260733, 321002215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13760 = ⟨810420398, 1427461404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14080 = ⟨907734057, 1982459870⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7040]
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

theorem power_14336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14336 = ⟨1731306458, 1551812567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14784 = ⟨1879071391, 1829202452⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15232 = ⟨1395708858, 1497177230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15296 = ⟨487831876, 2068089277⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15360 = ⟨1368263916, 2076980552⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15808 = ⟨1522548683, 2001077972⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7904]
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

theorem power_17280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17280 = ⟨1405370388, 1401549109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18176 = ⟨277390402, 1017102786⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18304 = ⟨1476748888, 884639226⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19328 = ⟨1574695602, 343473568⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19968 = ⟨1443152952, 1248797592⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9984]
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

theorem power_21376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21376 = ⟨1307076942, 7561917⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22272 = ⟨1233494247, 815501048⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22400 = ⟨573590654, 1886827735⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23424 = ⟨1958385928, 881847861⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23552 = ⟨1609631824, 2034059636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11776]
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

theorem power_25472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25472 = ⟨1174190859, 1895341634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26368 = ⟨231300344, 22616870⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26496 = ⟨367539449, 193384522⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27520 = ⟨958142641, 463023983⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28160 = ⟨1780266745, 1890401423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14080]
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

theorem power_28673 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28673 = ⟨14184575, 310232666⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29568 = ⟨1143577263, 1687775453⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30464 = ⟨1306202290, 656337007⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30592 = ⟨1770822168, 126575104⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30720 = ⟨1155186462, 790771269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31616 = ⟨2038041307, 395046603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15808]
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

theorem power_34560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34560 = ⟨989291292, 715603760⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36352 = ⟨1666103267, 543807372⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36608 = ⟨1237538406, 1195917052⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38656 = ⟨1994929345, 92888755⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39936 = ⟨602433585, 1609250172⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19968]
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

theorem power_42752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42752 = ⟨1211674855, 376154875⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44544 = ⟨2059734770, 1626927132⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44800 = ⟨242848192, 1491966760⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46848 = ⟨1260104520, 1620860171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47104 = ⟨496848496, 890027025⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23552]
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

theorem power_50944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50944 = ⟨892010052, 235679077⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52736 = ⟨559851472, 639516914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52992 = ⟨1477173668, 1592872585⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55040 = ⟨690580754, 1235284839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56320 = ⟨711796573, 1765055593⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28160]
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

theorem power_57346 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57346 = ⟨260151801, 511186506⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28673]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59136 = ⟨195201793, 97887997⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60928 = ⟨704349578, 1737110009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61184 = ⟨1544835842, 1484496856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61441 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61441 = ⟨54833272, 934099980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63232 = ⟨620105848, 1681908103⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31616]
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

theorem power_69120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69120 = ⟨1663137283, 90268489⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72704 = ⟨1659670602, 561643989⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73216 = ⟨639455891, 1442019586⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77312 = ⟨105480201, 1515380487⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_79872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79872 = ⟨1721053354, 1645226881⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39936]
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

theorem power_85504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 85504 = ⟨1880924448, 411348355⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89088 = ⟨1042833731, 101065615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89600 = ⟨943470255, 773386671⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_93696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93696 = ⟨1605856742, 1072957887⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94209 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94209 = ⟨497103150, 1029891871⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47104]
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

theorem power_101888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101888 = ⟨1373722145, 1666977548⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105472 = ⟨652753676, 326975263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105984 = ⟨1326715095, 1134353850⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_110080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110080 = ⟨1592908054, 239121665⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_112640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112640 = ⟨983493989, 1661572926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56320]
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

theorem power_114692 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114692 = ⟨1927081727, 2050336903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57346]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_118272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118272 = ⟨530163866, 642094632⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121856 = ⟨1209236572, 1025248382⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122368 = ⟨183438626, 1151491724⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122882 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122882 = ⟨318057155, 372288421⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61441]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126464 = ⟨1689711892, 426618051⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126977 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126977 = ⟨1750459979, 181711770⟩ := by
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

theorem power_138240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 138240 = ⟨65347242, 2130122093⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_145408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 145408 = ⟨477007636, 1158627154⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_146432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 146432 = ⟨2123620430, 1690710365⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_154624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 154624 = ⟨1660165387, 1203252895⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_159745 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 159745 = ⟨1370470202, 927484434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79872]
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

theorem power_171008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 171008 = ⟨221694143, 1124421163⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_178176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 178176 = ⟨942015741, 884128330⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_179200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 179200 = ⟨752234394, 244937601⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_187392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 187392 = ⟨321515844, 1267053385⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_188418 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 188418 = ⟨810873620, 1131305431⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94209]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_192513 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 192513 = ⟨1253180392, 1816513946⟩ := by
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

theorem power_203776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 203776 = ⟨851041255, 34490752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_210944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 210944 = ⟨1583620585, 920603234⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_211968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 211968 = ⟨186431743, 1909359341⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_220160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 220160 = ⟨1138662242, 1124185095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_225281 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 225281 = ⟨1102939442, 776360845⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112640]
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

theorem power_229384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 229384 = ⟨1358189085, 2073966069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114692]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_236544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 236544 = ⟨366429576, 528662537⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_243712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 243712 = ⟨894328797, 399061936⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_244736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 244736 = ⟨1580147207, 1037897828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_245764 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 245764 = ⟨509785162, 182211273⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122882]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_252928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 252928 = ⟨614226948, 186141612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_253954 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 253954 = ⟨67720113, 21373326⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126977]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_258049 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 258049 = ⟨1000407407, 487795194⟩ := by
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

theorem power_276480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 276480 = ⟨937246950, 1944723122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_138240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_290817 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 290817 = ⟨1101133723, 148050506⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_145408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_292864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 292864 = ⟨1183893609, 1128652358⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_146432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_309248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 309248 = ⟨830880001, 1851760075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_154624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_319490 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 319490 = ⟨1495440514, 1439863254⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_159745]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_323585 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 323585 = ⟨2050048117, 1734599244⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_161792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_325632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 325632 = ⟨1854849082, 2091484047⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_162816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_342016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 342016 = ⟨1790471539, 839403197⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_171008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_356353 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 356353 = ⟨573656418, 849566343⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_178176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_358400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 358400 = ⟨1007493001, 1726918802⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_179200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_374784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 374784 = ⟨202323676, 882237532⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_187392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_376836 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 376836 = ⟨2086523006, 1339062251⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_188418]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_385026 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 385026 = ⟨1955339437, 1373381018⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_192513]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_389121 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 389121 = ⟨1614026068, 207609758⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_194560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_391168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 391168 = ⟨298589147, 981397056⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_195584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_407552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 407552 = ⟨1102747704, 1680525000⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_203776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_421889 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 421889 = ⟨1088763298, 1489579132⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_210944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_423936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 423936 = ⟨1356662908, 725095927⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_211968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_440320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 440320 = ⟨411614884, 176236651⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_220160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_450562 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 450562 = ⟨1841898316, 1308858860⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_225281]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_454657 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 454657 = ⟨965326167, 1958759429⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_227328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_456704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 456704 = ⟨736440378, 211006336⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_228352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_458768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 458768 = ⟨1772331148, 1942936253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_229384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_473088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 473088 = ⟨1645824567, 173000716⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_236544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_487425 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 487425 = ⟨1083102758, 205971595⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_243712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_489472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 489472 = ⟨1489653516, 1781773511⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_244736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_491528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 491528 = ⟨1303211014, 517376761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_245764]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_505856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 505856 = ⟨1624712612, 1864287004⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_252928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_507908 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 507908 = ⟨199077011, 147655676⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_253954]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_516098 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 516098 = ⟨651070449, 8202843⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_258049]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_520193 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 520193 = ⟨1392150456, 1085374405⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_260096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_522240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 522240 = ⟨50276117, 2135200447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_261120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_552961 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 552961 = ⟨1598299974, 1299442056⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_276480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_581634 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 581634 = ⟨1882425481, 453223757⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_290817]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_585729 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 585729 = ⟨920728386, 361256397⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_292864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_618497 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 618497 = ⟨70018993, 322980891⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_309248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_638980 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 638980 = ⟨680638985, 1274554851⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_319490]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_647170 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 647170 = ⟨1800754839, 1223741812⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_323585]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_651265 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 651265 = ⟨547568765, 1117835110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_325632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_684033 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 684033 = ⟨1515133029, 326618407⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_342016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_712706 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 712706 = ⟨269794106, 675434431⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_356353]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_716801 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 716801 = ⟨661959376, 449563461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_358400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_749569 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 749569 = ⟨760446580, 327952100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_374784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_753672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 753672 = ⟨1549667701, 938136221⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_376836]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_770052 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 770052 = ⟨622441603, 811683139⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_385026]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_778242 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 778242 = ⟨1751789950, 1147440418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_389121]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_782337 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 782337 = ⟨345991246, 1720062462⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_391168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_815105 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 815105 = ⟨566842249, 1983605092⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_407552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_843778 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 843778 = ⟨1072600367, 451333031⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_421889]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_847873 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 847873 = ⟨1119691208, 1581098202⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_423936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_880641 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 880641 = ⟨461657658, 136103689⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_440320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_901124 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 901124 = ⟨280974717, 10828957⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_450562]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_909314 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 909314 = ⟨1591655026, 1183004556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_454657]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_913409 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 913409 = ⟨215895566, 2044121891⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_456704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_917536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 917536 = ⟨206381635, 293663471⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_458768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_946177 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 946177 = ⟨1668918163, 1231187385⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_473088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_974850 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 974850 = ⟨1270220380, 1258902565⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_487425]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_978945 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 978945 = ⟨9103087, 1523989855⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_489472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_983056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 983056 = ⟨1906917922, 994593500⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_491528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1011713 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1011713 = ⟨969764528, 1178321088⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_505856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1015816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1015816 = ⟨444263409, 2119179583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_507908]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1032196 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1032196 = ⟨943657605, 107509358⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_516098]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1040386 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1040386 = ⟨1648163068, 1217272688⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_520193]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1044481 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1044481 = ⟨1402182598, 1257043772⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_522240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1105922 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1105922 = ⟨936547234, 1635591687⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_552961]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1163268 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1163268 = ⟨1669609984, 898817594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_581634]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1171458 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1171458 = ⟨664656115, 1296873637⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_585729]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1236994 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1236994 = ⟨771062918, 1588615036⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_618497]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1277960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1277960 = ⟨1149082877, 127853367⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_638980]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1294340 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1294340 = ⟨1663133045, 1647110028⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_647170]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1302530 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1302530 = ⟨999720678, 807449048⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_651265]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1368066 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1368066 = ⟨683738638, 2022291601⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_684033]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1425412 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1425412 = ⟨403043995, 2122500858⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_712706]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1433602 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1433602 = ⟨1797185718, 1055084604⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_716801]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1499138 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1499138 = ⟨729194463, 452704858⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_749569]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1507344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1507344 = ⟨2056331225, 1242050795⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_753672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1540104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1540104 = ⟨1396619547, 1767700915⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_770052]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1556484 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1556484 = ⟨1982645525, 1086247485⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_778242]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1564674 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1564674 = ⟨1567366594, 316577939⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_782337]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1630210 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1630210 = ⟨1184781847, 392180809⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_815105]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1687556 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1687556 = ⟨2021960796, 20096709⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_843778]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1695746 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1695746 = ⟨1361222935, 1492900458⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_847873]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1761282 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1761282 = ⟨361415852, 763962964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_880641]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1802248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1802248 = ⟨512124114, 1846456438⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_901124]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1818628 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1818628 = ⟨1201995862, 149620442⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_909314]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1826818 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1826818 = ⟨314536698, 1297869103⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_913409]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1835072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1835072 = ⟨1411712224, 2032790313⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_917536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1892354 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1892354 = ⟨1183104751, 110161156⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_946177]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1949700 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1949700 = ⟨1065453243, 168202032⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_974850]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1957890 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1957890 = ⟨335401912, 1031696667⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_978945]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1966112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1966112 = ⟨365857330, 2106441412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_983056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2023426 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2023426 = ⟨1605104274, 1589424264⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1011713]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2031632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2031632 = ⟨1766161803, 1222107361⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1015816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2064392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2064392 = ⟨1325961410, 1224228507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1032196]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2080772 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2080772 = ⟨1197302970, 953007618⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1040386]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2088962 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2088962 = ⟨1031727810, 313604120⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1044481]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2211844 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2211844 = ⟨2122811295, 1452571409⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1105922]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2326536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2326536 = ⟨1426465951, 1741694777⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1163268]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2342916 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2342916 = ⟨1347932936, 662200320⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1171458]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2473988 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2473988 = ⟨52236546, 1152575134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1236994]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2555920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2555920 = ⟨2012907573, 1490413861⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1277960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2588680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2588680 = ⟨910848577, 1038667503⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1294340]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2605060 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2605060 = ⟨2025199624, 1524434469⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1302530]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2736132 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2736132 = ⟨477421377, 186292719⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1368066]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2850824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2850824 = ⟨1211956531, 230365323⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1425412]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2867204 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2867204 = ⟨1528385806, 384923345⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1433602]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2998276 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2998276 = ⟨2086259507, 1297455495⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1499138]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3014688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3014688 = ⟨1112219234, 1907971340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1507344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3080208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3080208 = ⟨1310654280, 675362918⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1540104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3112968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3112968 = ⟨1075305857, 1197833780⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1556484]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3129348 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3129348 = ⟨782891816, 763618025⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1564674]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3260420 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3260420 = ⟨949669933, 1716617024⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1630210]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3375112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3375112 = ⟨1221204866, 434768379⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1687556]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3391492 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3391492 = ⟨937304188, 1881023408⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1695746]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3522564 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3522564 = ⟨944760082, 1558175004⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1761282]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3604496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3604496 = ⟨1705546050, 570142833⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1802248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3637256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3637256 = ⟨367786988, 1223185419⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1818628]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3653636 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3653636 = ⟨1591551398, 435981991⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1826818]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3670144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3670144 = ⟨1079036469, 1507584477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1835072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3784708 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3784708 = ⟨527612738, 97034036⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1892354]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3899400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3899400 = ⟨1908449429, 2077110118⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1949700]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3915780 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3915780 = ⟨2010139876, 2026407336⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1957890]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3932224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3932224 = ⟨1435633858, 859932290⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1966112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4046852 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4046852 = ⟨818740385, 541661284⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2023426]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4063264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4063264 = ⟨237396566, 790967018⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2031632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4128784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4128784 = ⟨361680012, 1283028039⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2064392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4161544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4161544 = ⟨1428123149, 808766993⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2080772]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4177924 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4177924 = ⟨2140496184, 146464590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2088962]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4423688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4423688 = ⟨624750214, 1498839060⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2211844]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4653072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4653072 = ⟨374769503, 976169937⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2326536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4685832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4685832 = ⟨531130520, 1465033160⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2342916]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4947976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4947976 = ⟨1330728658, 1284517017⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2473988]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5111840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5111840 = ⟨216282417, 2031572858⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2555920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5177360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5177360 = ⟨120709224, 1932944300⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2588680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5210120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5210120 = ⟨1055908023, 921977982⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2605060]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5472264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5472264 = ⟨668710342, 1228437417⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2736132]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5701648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5701648 = ⟨104145955, 129373880⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2850824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5734408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5734408 = ⟨1182253579, 991144238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2867204]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5996552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5996552 = ⟨387729844, 800563155⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2998276]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6029376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6029376 = ⟨1991868892, 2091419665⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3014688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6160416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6160416 = ⟨1178379714, 605415744⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3080208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6225936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6225936 = ⟨1507572201, 621221424⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3112968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6258696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6258696 = ⟨74778879, 1291680968⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3129348]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6520840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6520840 = ⟨1357558428, 1525517507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3260420]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6750224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6750224 = ⟨1795332137, 1029846521⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3375112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6782984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6782984 = ⟨1998799589, 222141088⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3391492]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7045128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7045128 = ⟨1303813923, 437191209⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3522564]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7208992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7208992 = ⟨999387260, 401715335⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3604496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7274512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7274512 = ⟨1843627667, 877893100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3637256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7307272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7307272 = ⟨1759996423, 1268777855⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3653636]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7340288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7340288 = ⟨1112627287, 1183642156⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3670144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7569416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7569416 = ⟨653716764, 2033162804⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3784708]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7798800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7798800 = ⟨1722001477, 1515149727⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3899400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7831560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7831560 = ⟨1669175812, 2007484564⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3915780]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7864448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7864448 = ⟨361929347, 1283979307⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3932224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8093704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8093704 = ⟨419481089, 2079574145⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4046852]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8126528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8126528 = ⟨29150162, 1742587617⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4063264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8257568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8257568 = ⟨348245497, 1957614003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4128784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8323088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8323088 = ⟨1646388499, 951015393⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4161544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8355848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8355848 = ⟨1049440000, 1429078417⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4177924]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8847376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8847376 = ⟨1740999188, 321253473⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4423688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9306144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9306144 = ⟨647928975, 1609815202⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4653072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9371664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9371664 = ⟨337679608, 1195666299⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4685832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9895952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9895952 = ⟨211708522, 2104206036⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4947976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10223680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10223680 = ⟨1195599982, 1591486694⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5111840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10354720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10354720 = ⟨970679412, 1734981700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5177360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10420240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10420240 = ⟨1003080729, 711264162⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5210120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10944528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10944528 = ⟨1149100562, 55433607⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5472264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11403296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11403296 = ⟨1070193783, 1528655766⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5701648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11468816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11468816 = ⟨1211380097, 300568235⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5734408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11993104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11993104 = ⟨562605721, 1153575793⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5996552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12058752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12058752 = ⟨1609372335, 1453133362⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6029376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12320832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12320832 = ⟨966537752, 1836854814⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6160416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12451872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12451872 = ⟨964377488, 789888522⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6225936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12517392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12517392 = ⟨1662866213, 217561207⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6258696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13041680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13041680 = ⟨1776859473, 1354046441⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6520840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13500448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13500448 = ⟨890640902, 773040385⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6750224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13565968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13565968 = ⟨1643705827, 341244233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6782984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14090256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14090256 = ⟨1270773144, 549056329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7045128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14417984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14417984 = ⟨1127934470, 1976589101⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7208992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14549024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14549024 = ⟨2005834774, 1263640285⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7274512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14614544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14614544 = ⟨353039803, 550294903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7307272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14680576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14680576 = ⟨130812089, 322821994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7340288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15138832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15138832 = ⟨1385343074, 1000724193⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7569416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15597600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15597600 = ⟨160206861, 968254998⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7798800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15663120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15663120 = ⟨1405823771, 756724365⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7831560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15728896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15728896 = ⟨950092617, 580101218⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7864448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16187408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16187408 = ⟨537899700, 1954272976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8093704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16253056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16253056 = ⟨1165591509, 9239680⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8126528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16515136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16515136 = ⟨1158734845, 1168807028⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8257568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16646176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16646176 = ⟨1715068495, 1613502788⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8323088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16711696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16711696 = ⟨1516552834, 764262254⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8355848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17694752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17694752 = ⟨1925536071, 124537884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8847376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18612288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18612288 = ⟨1070797505, 661360618⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9306144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18743328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18743328 = ⟨800312880, 1577066494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9371664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19791904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19791904 = ⟨1889851340, 1986332763⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9895952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20447360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20447360 = ⟨2142565690, 1282550859⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10223680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20709440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20709440 = ⟨269706274, 966313424⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10354720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20840480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20840480 = ⟨130957688, 467959084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10420240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21889056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21889056 = ⟨62655112, 342108628⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10944528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22806592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22806592 = ⟨1158243675, 897837469⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11403296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22937632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22937632 = ⟨1030414324, 2045702929⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11468816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23986208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23986208 = ⟨1759168214, 289177513⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11993104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24117504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24117504 = ⟨109929704, 1730046032⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12058752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24641664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24641664 = ⟨1106672366, 2087332629⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12320832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24903744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24903744 = ⟨135778657, 1121159215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12451872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25034784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25034784 = ⟨944033116, 1245945558⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12517392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26083360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26083360 = ⟨1697596821, 315688820⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13041680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27000896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27000896 = ⟨459477763, 1134842239⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13500448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27131936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27131936 = ⟨1240662111, 2046214771⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13565968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28180512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28180512 = ⟨15544039, 1855727929⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14090256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28835968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28835968 = ⟨1340964991, 1184439599⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14417984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29098048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29098048 = ⟨1451046400, 730086953⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14549024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29229088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29229088 = ⟨534913108, 971666902⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14614544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29361152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29361152 = ⟨188438465, 212575099⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14680576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30277664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30277664 = ⟨2006624916, 1587085013⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15138832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31195200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31195200 = ⟨335150732, 1275823484⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15597600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31326240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31326240 = ⟨970827381, 1346950748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15663120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31457792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31457792 = ⟨2032034231, 1109089149⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15728896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32374816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32374816 = ⟨1807569836, 1805242926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16187408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32506112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32506112 = ⟨904284524, 1721776361⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16253056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33030272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33030272 = ⟨601735200, 404582439⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16515136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33292352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33292352 = ⟨197058993, 1626260883⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16646176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33423392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33423392 = ⟨1650365879, 1949828491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16711696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35389504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35389504 = ⟨1386369529, 191199951⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17694752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37224576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37224576 = ⟨313634829, 527944362⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18612288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37486656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37486656 = ⟨1576051197, 986510831⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18743328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39583808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39583808 = ⟨752038143, 168291267⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19791904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40894720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40894720 = ⟨532959022, 2022069736⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20447360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41418880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41418880 = ⟨209117432, 309768236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20709440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41680960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41680960 = ⟨2091911046, 201102060⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20840480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43778112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43778112 = ⟨1351981561, 1715576011⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21889056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45613184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45613184 = ⟨2005278878, 1793198792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22806592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45875264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45875264 = ⟨1055288961, 336483461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22937632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47972416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47972416 = ⟨1771661276, 1051727262⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23986208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48235008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48235008 = ⟨1599594443, 1531591770⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24117504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49283328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49283328 = ⟨1960561020, 2098141660⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24641664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49807488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49807488 = ⟨912329398, 2039431496⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24903744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50069568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50069568 = ⟨749839223, 1878517487⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25034784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52166720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52166720 = ⟨54044667, 2007956161⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26083360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54001792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54001792 = ⟨992941434, 1763625889⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27000896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54263872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54263872 = ⟨438712833, 1315101893⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27131936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56361024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56361024 = ⟨1084168160, 298241078⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28180512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57671936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57671936 = ⟨2132558999, 206238055⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28835968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58196096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58196096 = ⟨61437463, 1158816392⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29098048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58458176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58458176 = ⟨1890346340, 503645877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29229088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60555328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60555328 = ⟨1727425341, 1650892899⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30277664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62390400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62390400 = ⟨1763735750, 879789704⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31195200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62652480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62652480 = ⟨214807317, 872557398⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31326240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62915584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62915584 = ⟨2039959946, 1457037680⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31457792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64749632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64749632 = ⟨335623930, 1443609635⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32374816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65012224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65012224 = ⟨597832026, 180280130⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32506112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66060544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66060544 = ⟨586781303, 175124769⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33030272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66584704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66584704 = ⟨26283941, 997703657⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33292352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66846784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66846784 = ⟨1662470123, 255935839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33423392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_70779008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70779008 = ⟨628659743, 2077413758⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35389504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_74449152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 74449152 = ⟨59613612, 421094432⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37224576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_74973312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 74973312 = ⟨1872971673, 585343796⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37486656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_79167616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79167616 = ⟨182081607, 648632923⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39583808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_81789440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81789440 = ⟨94330721, 811520384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40894720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_82837760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 82837760 = ⟨1460883884, 107667972⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41418880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_83361920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83361920 = ⟨1138570649, 407702454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41680960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87556224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87556224 = ⟨1449297666, 1042068392⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43778112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_91226368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 91226368 = ⟨2052564332, 1924373164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45613184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_91750528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 91750528 = ⟨886042054, 1707446795⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45875264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_95944832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 95944832 = ⟨1014126239, 1247113654⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47972416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_96470016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96470016 = ⟨558100220, 1980501108⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48235008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98566656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98566656 = ⟨1188533579, 1610440034⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49283328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_99614976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 99614976 = ⟨2062665726, 1218683628⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49807488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_100139136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100139136 = ⟨1427353714, 356270733⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50069568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104333440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104333440 = ⟨473719320, 1019063156⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52166720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108003584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108003584 = ⟨2012049027, 454441233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54001792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108527744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108527744 = ⟨2106592758, 391248120⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54263872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_112722048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112722048 = ⟨372491066, 295571259⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56361024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115343872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115343872 = ⟨1195728598, 1771676800⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57671936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_116392192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116392192 = ⟨1441009639, 1822118243⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58196096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_116916352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116916352 = ⟨325931360, 55162934⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58458176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121110656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121110656 = ⟨1777681325, 1871552550⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60555328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124780800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124780800 = ⟨1503858443, 609407568⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62390400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125304960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125304960 = ⟨207648698, 320401590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62652480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_129499264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 129499264 = ⟨432380585, 225805632⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64749632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_130024448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 130024448 = ⟨1252927563, 799345076⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65012224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_132121088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 132121088 = ⟨1236328312, 138256170⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66060544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_133169408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 133169408 = ⟨130503161, 1782667569⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66584704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_133693568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 133693568 = ⟨508064361, 1057002066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66846784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_141558016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 141558016 = ⟨740360265, 623743836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70779008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_148898304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 148898304 = ⟨190191541, 917735177⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74449152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_149946624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 149946624 = ⟨544502734, 565427714⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74973312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_158335232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 158335232 = ⟨143715297, 1704528583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79167616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_163578880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 163578880 = ⟨1351399750, 1217896196⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81789440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_165675520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 165675520 = ⟨967123712, 268007561⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82837760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_166723840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 166723840 = ⟨515608496, 150078005⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83361920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_175112448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 175112448 = ⟨1846516363, 2120494851⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87556224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_182452736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 182452736 = ⟨2121755091, 957852824⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91226368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_183501056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 183501056 = ⟨1370288178, 936080076⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91750528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_191889664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 191889664 = ⟨1324194864, 450260861⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_95944832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_197133312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 197133312 = ⟨209663158, 168116384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98566656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_199229952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 199229952 = ⟨1830755305, 1206160913⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99614976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_200278272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 200278272 = ⟨774518853, 1683338854⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100139136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_208666880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 208666880 = ⟨1310839628, 1946238892⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104333440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_216007168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 216007168 = ⟨289411553, 2080690834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108003584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_217055488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 217055488 = ⟨1499319184, 429147243⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108527744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_225444096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 225444096 = ⟨867078748, 40983978⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112722048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_230687744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 230687744 = ⟨1012525923, 71691935⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115343872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_232784384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 232784384 = ⟨1747893200, 2079311632⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116392192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_233832704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 233832704 = ⟨1361144585, 14144748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116916352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_242221312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 242221312 = ⟨964196300, 1420440122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121110656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_249561600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 249561600 = ⟨458470969, 2021862096⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124780800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_250609920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 250609920 = ⟨1768006804, 205025981⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125304960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_258998528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 258998528 = ⟨1500793362, 1130783953⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_129499264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_264242176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 264242176 = ⟨1157494553, 1817015079⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_132121088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_266338816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 266338816 = ⟨1403850513, 1923650652⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133169408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_267387136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 267387136 = ⟨1656200037, 1421387039⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133693568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_283116032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 283116032 = ⟨1947310857, 1800964977⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_141558016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_297796608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 297796608 = ⟨2107512806, 635240816⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_148898304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_299893248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 299893248 = ⟨1587198777, 2095237372⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_149946624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_316670464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 316670464 = ⟨236141218, 776436722⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_158335232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_331351040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 331351040 = ⟨2038288495, 670227777⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_165675520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_333447680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 333447680 = ⟨105786977, 1425270556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_166723840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_350224896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 350224896 = ⟨410039806, 957328063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_175112448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_364905472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 364905472 = ⟨2109249359, 247223496⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_182452736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_367002112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 367002112 = ⟨2035754708, 1678481701⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_183501056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_383779328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 383779328 = ⟨28029151, 584393300⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_191889664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_398459904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 398459904 = ⟨419428947, 1890870518⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_199229952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_400556544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 400556544 = ⟨1062293998, 1608040076⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_200278272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_417333760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 417333760 = ⟨1331642889, 933899101⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_208666880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_432014336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 432014336 = ⟨740661540, 1927215114⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_216007168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_434110976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 434110976 = ⟨1304742302, 717510228⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_217055488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_450888192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 450888192 = ⟨188102543, 560085664⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_225444096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_465568768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 465568768 = ⟨984290948, 99941766⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_232784384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_467665408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 467665408 = ⟨1425913091, 957602501⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_233832704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_484442624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 484442624 = ⟨1916407108, 1616440004⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_242221312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_499123200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 499123200 = ⟨1828798623, 27117548⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_249561600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_501219840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 501219840 = ⟨1097917470, 94376897⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_250609920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_517997056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 517997056 = ⟨1887769558, 978050351⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_258998528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_532677632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 532677632 = ⟨891334987, 1040656207⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_266338816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_534774272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 534774272 = ⟨1370965589, 1118150395⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_267387136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_566232064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 566232064 = ⟨212575099, 1959045182⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_283116032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_599786496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 599786496 = ⟨1457037680, 107523701⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_299893248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_633340928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 633340928 = ⟨1980501108, 1589383427⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_316670464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_666895360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 666895360 = ⟨799345076, 894556084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_333447680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_700449792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 700449792 = ⟨1217896196, 796083897⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_350224896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_734004224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 734004224 = ⟨168116384, 1937820489⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_367002112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_767558656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 767558656 = ⟨71691935, 1134957724⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_383779328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_801113088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 801113088 = ⟨1817015079, 989989094⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_400556544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_834667520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 834667520 = ⟨635240816, 39970841⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_417333760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_868221952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 868221952 = ⟨670227777, 109195152⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_434110976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_901776384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 901776384 = ⟨247223496, 38234288⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_450888192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_935330816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 935330816 = ⟨1890870518, 1728054700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_467665408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_968885248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 968885248 = ⟨1927215114, 1406822107⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_484442624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1002439680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1002439680 = ⟨99941766, 1163192699⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_501219840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1035994112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1035994112 = ⟨27117548, 318685024⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_517997056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1069548544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1069548544 = ⟨1040656207, 1256148660⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_534774272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 224) = ⟨188438465, 212575099⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 224 = 29361152 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_29361152

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨188438465, 212575099⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 224) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 225) = ⟨212575099, 1959045182⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 225 = 566232064 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_566232064

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨212575099, 1959045182⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 225) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 226) = ⟨2107512806, 635240816⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 226 = 297796608 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_297796608

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2107512806, 635240816⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 226) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 227) = ⟨635240816, 39970841⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 227 = 834667520 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_834667520

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨635240816, 39970841⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 227) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 228) = ⟨1351399750, 1217896196⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 228 = 163578880 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_163578880

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1351399750, 1217896196⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 228) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 229) = ⟨1217896196, 796083897⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 229 = 700449792 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_700449792

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1217896196, 796083897⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 229) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 230) = ⟨740661540, 1927215114⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 230 = 432014336 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_432014336

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨740661540, 1927215114⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 230) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 231) = ⟨1927215114, 1406822107⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 231 = 968885248 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_968885248

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1927215114, 1406822107⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 231) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 232) = ⟨558100220, 1980501108⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 232 = 96470016 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_96470016

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨558100220, 1980501108⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 232) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 233) = ⟨1980501108, 1589383427⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 233 = 633340928 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_633340928

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1980501108, 1589383427⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 233) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 234) = ⟨2109249359, 247223496⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 234 = 364905472 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_364905472

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2109249359, 247223496⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 234) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 235) = ⟨247223496, 38234288⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 235 = 901776384 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_901776384

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨247223496, 38234288⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 235) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 236) = ⟨1012525923, 71691935⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 236 = 230687744 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_230687744

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1012525923, 71691935⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 236) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 237) = ⟨71691935, 1134957724⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 237 = 767558656 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_767558656

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨71691935, 1134957724⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 237) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 238) = ⟨1828798623, 27117548⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 238 = 499123200 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_499123200

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1828798623, 27117548⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 238) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 239) = ⟨27117548, 318685024⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 239 = 1035994112 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1035994112

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨27117548, 318685024⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 239) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 240) = ⟨2039959946, 1457037680⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 240 = 62915584 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_62915584

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2039959946, 1457037680⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 240) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 241) = ⟨1457037680, 107523701⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 241 = 599786496 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_599786496

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1457037680, 107523701⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 241) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 242) = ⟨2038288495, 670227777⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 242 = 331351040 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_331351040

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2038288495, 670227777⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 242) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 243) = ⟨670227777, 109195152⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 243 = 868221952 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_868221952

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨670227777, 109195152⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 243) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 244) = ⟨209663158, 168116384⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 244 = 197133312 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_197133312

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨209663158, 168116384⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 244) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 245) = ⟨168116384, 1937820489⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 245 = 734004224 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_734004224

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨168116384, 1937820489⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 245) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 246) = ⟨984290948, 99941766⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 246 = 465568768 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_465568768

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨984290948, 99941766⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 246) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 247) = ⟨99941766, 1163192699⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 247 = 1002439680 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1002439680

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨99941766, 1163192699⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 247) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 248) = ⟨1252927563, 799345076⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 248 = 130024448 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_130024448

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1252927563, 799345076⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 248) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 249) = ⟨799345076, 894556084⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 249 = 666895360 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_666895360

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨799345076, 894556084⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 249) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 250) = ⟨419428947, 1890870518⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 250 = 398459904 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_398459904

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨419428947, 1890870518⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 250) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 251) = ⟨1890870518, 1728054700⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 251 = 935330816 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_935330816

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1890870518, 1728054700⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 251) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 252) = ⟨1157494553, 1817015079⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 252 = 264242176 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_264242176

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1157494553, 1817015079⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 252) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 253) = ⟨1817015079, 989989094⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 253 = 801113088 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_801113088

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1817015079, 989989094⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 253) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 254) = ⟨891334987, 1040656207⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 254 = 532677632 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_532677632

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨891334987, 1040656207⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 254) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 255) = ⟨1040656207, 1256148660⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 255 = 1069548544 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1069548544

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1040656207, 1256148660⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 255) := by
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

end R17TableAChunk07Certificate
