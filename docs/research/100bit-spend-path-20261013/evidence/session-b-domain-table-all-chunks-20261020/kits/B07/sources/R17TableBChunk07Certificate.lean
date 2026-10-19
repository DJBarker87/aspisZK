import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableBChunk07Certificate
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

theorem power_28672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28672 = ⟨1124768046, 299494314⟩ := by
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

theorem power_57344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57344 = ⟨347749121, 1576860820⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28672]
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

theorem power_61440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61440 = ⟨1168068815, 1631133982⟩ := by
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

theorem power_94208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94208 = ⟨1753543609, 1294275673⟩ := by
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

theorem power_122880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122880 = ⟨1829052821, 673049321⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126464 = ⟨1689711892, 426618051⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63232]
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

theorem power_159744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 159744 = ⟨1924483244, 1528988896⟩ := by
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

theorem power_188416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 188416 = ⟨1213375404, 771547637⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94208]
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

theorem power_225280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 225280 = ⟨122809504, 181977862⟩ := by
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

theorem power_252928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 252928 = ⟨614226948, 186141612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_253952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 253952 = ⟨44588143, 2058311453⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126976]
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

theorem power_276480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 276480 = ⟨937246950, 1944723122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_138240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_290816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 290816 = ⟨1458581325, 1279621404⟩ := by
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

theorem power_319488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 319488 = ⟨1565145988, 1765289675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_159744]
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

theorem power_342016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 342016 = ⟨1790471539, 839403197⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_171008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_356352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 356352 = ⟨128738146, 457848703⟩ := by
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

theorem power_385024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 385024 = ⟨914918274, 1369105915⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_192512]
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

theorem power_407552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 407552 = ⟨1102747704, 1680525000⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_203776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_421888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 421888 = ⟨1212320872, 1495300507⟩ := by
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

theorem power_450560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 450560 = ⟨818224288, 1972399941⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_225280]
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

theorem power_473088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 473088 = ⟨1645824567, 173000716⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_236544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_487424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 487424 = ⟨1300871249, 1490001285⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_243712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_489472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 489472 = ⟨1489653516, 1781773511⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_244736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_505856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 505856 = ⟨1624712612, 1864287004⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_252928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_516096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 516096 = ⟨1444319707, 1095294811⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_258048]
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

theorem power_552960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 552960 = ⟨333636023, 948573238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_276480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_581632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 581632 = ⟨1616101075, 811514491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_290816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_585728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 585728 = ⟨1272345615, 2072662117⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_292864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_618496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 618496 = ⟨1573749961, 753946855⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_309248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_647168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 647168 = ⟨1213735332, 1357695652⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_323584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_651264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 651264 = ⟨274337143, 1881376116⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_325632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_684032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 684032 = ⟨841695573, 113926739⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_342016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_712704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 712704 = ⟨494233883, 1403803427⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_356352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_716800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 716800 = ⟨401706099, 967129345⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_358400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_749568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 749568 = ⟨895013455, 284231781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_374784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_778240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 778240 = ⟨1408222478, 1721187542⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_389120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_782336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 782336 = ⟨18011247, 565274326⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_391168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_815104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 815104 = ⟨994459063, 1883501554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_407552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_843776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 843776 = ⟨920245660, 938576836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_421888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_847872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 847872 = ⟨854296756, 1657148963⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_423936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_880640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 880640 = ⟨1104635206, 858881536⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_440320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_909312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 909312 = ⟨919065681, 1216872295⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_454656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_913408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 913408 = ⟨936298450, 1105042578⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_456704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_946176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 946176 = ⟨1994468584, 1611997849⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_473088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_974848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 974848 = ⟨1757257503, 734249953⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_487424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_978944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 978944 = ⟨702523908, 198087577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_489472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1011712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1011712 = ⟨277472845, 620479805⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_505856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1040384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1040384 = ⟨570004307, 1164891669⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_520192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1044480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1044480 = ⟨1807661853, 544066780⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_522240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1105920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1105920 = ⟨1986804722, 1373191730⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_552960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1171456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1171456 = ⟨1765843037, 2085683345⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_585728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1236992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1236992 = ⟨2064624001, 245417806⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_618496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1302528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1302528 = ⟨888152082, 1321895104⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_651264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1368064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1368064 = ⟨365445058, 1099441367⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_684032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1433600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1433600 = ⟨1478304746, 406667278⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_716800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1499136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1499136 = ⟨513998937, 202899553⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_749568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1564672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1564672 = ⟨1540140142, 751979754⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_782336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1630208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1630208 = ⟨147800194, 1069151092⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_815104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1695744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1695744 = ⟨1332929929, 2095879383⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_847872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1761280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1761280 = ⟨1661270250, 1697085245⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_880640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1826816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1826816 = ⟨210392081, 157752587⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_913408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1892352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1892352 = ⟨204640856, 2040419027⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_946176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1957888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1957888 = ⟨1932017562, 1757637245⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_978944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2023424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2023424 = ⟨1601634968, 1790370824⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1011712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2088960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2088960 = ⟨1090698404, 2001864991⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1044480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 224) = ⟨347749121, 1576860820⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 224 = 57344 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_57344

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨347749121, 1576860820⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 224) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 225) = ⟨1986804722, 1373191730⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 225 = 1105920 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1105920

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1986804722, 1373191730⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 225) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 226) = ⟨1616101075, 811514491⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 226 = 581632 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_581632

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1616101075, 811514491⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 226) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 227) = ⟨147800194, 1069151092⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 227 = 1630208 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1630208

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨147800194, 1069151092⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 227) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 228) = ⟨1565145988, 1765289675⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 228 = 319488 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_319488

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1565145988, 1765289675⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 228) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 229) = ⟨365445058, 1099441367⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 229 = 1368064 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1368064

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨365445058, 1099441367⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 229) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 230) = ⟨920245660, 938576836⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 230 = 843776 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_843776

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨920245660, 938576836⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 230) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 231) = ⟨204640856, 2040419027⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 231 = 1892352 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1892352

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨204640856, 2040419027⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 231) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 232) = ⟨1213375404, 771547637⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 232 = 188416 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_188416

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1213375404, 771547637⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 232) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 233) = ⟨2064624001, 245417806⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 233 = 1236992 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1236992

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2064624001, 245417806⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 233) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 234) = ⟨494233883, 1403803427⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 234 = 712704 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_712704

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨494233883, 1403803427⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 234) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 235) = ⟨1661270250, 1697085245⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 235 = 1761280 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1761280

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1661270250, 1697085245⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 235) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 236) = ⟨818224288, 1972399941⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 236 = 450560 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_450560

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨818224288, 1972399941⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 236) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 237) = ⟨513998937, 202899553⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 237 = 1499136 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1499136

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨513998937, 202899553⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 237) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 238) = ⟨1757257503, 734249953⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 238 = 974848 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_974848

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1757257503, 734249953⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 238) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 239) = ⟨1601634968, 1790370824⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 239 = 2023424 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2023424

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1601634968, 1790370824⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 239) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 240) = ⟨1829052821, 673049321⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 240 = 122880 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_122880

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1829052821, 673049321⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 240) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 241) = ⟨1765843037, 2085683345⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 241 = 1171456 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1171456

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1765843037, 2085683345⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 241) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 242) = ⟨1213735332, 1357695652⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 242 = 647168 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_647168

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1213735332, 1357695652⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 242) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 243) = ⟨1332929929, 2095879383⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 243 = 1695744 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1695744

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1332929929, 2095879383⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 243) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 244) = ⟨914918274, 1369105915⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 244 = 385024 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_385024

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨914918274, 1369105915⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 244) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 245) = ⟨1478304746, 406667278⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 245 = 1433600 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1433600

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1478304746, 406667278⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 245) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 246) = ⟨919065681, 1216872295⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 246 = 909312 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_909312

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨919065681, 1216872295⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 246) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 247) = ⟨1932017562, 1757637245⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 247 = 1957888 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1957888

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1932017562, 1757637245⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 247) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 248) = ⟨44588143, 2058311453⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 248 = 253952 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_253952

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨44588143, 2058311453⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 248) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 249) = ⟨888152082, 1321895104⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 249 = 1302528 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1302528

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨888152082, 1321895104⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 249) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 250) = ⟨1408222478, 1721187542⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 250 = 778240 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_778240

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1408222478, 1721187542⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 250) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 251) = ⟨210392081, 157752587⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 251 = 1826816 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1826816

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨210392081, 157752587⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 251) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 252) = ⟨1444319707, 1095294811⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 252 = 516096 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_516096

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1444319707, 1095294811⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 252) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 253) = ⟨1540140142, 751979754⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 253 = 1564672 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1564672

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1540140142, 751979754⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 253) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 254) = ⟨570004307, 1164891669⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 254 = 1040384 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1040384

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨570004307, 1164891669⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 254) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 255) = ⟨1090698404, 2001864991⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 255 = 2088960 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2088960

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1090698404, 2001864991⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 255) := by
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

end R17TableBChunk07Certificate
