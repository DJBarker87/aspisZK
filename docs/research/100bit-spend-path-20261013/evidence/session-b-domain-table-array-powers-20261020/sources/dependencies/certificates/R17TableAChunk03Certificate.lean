import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk03Certificate
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

theorem power_48 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48 = ⟨1179671875, 1031913030⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24]
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

theorem power_70 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70 = ⟨115184242, 829081638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35]
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

theorem power_86 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86 = ⟨1687815885, 1893568127⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87 = ⟨1648565317, 52537112⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88 = ⟨611478089, 464063968⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44]
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

theorem power_96 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96 = ⟨1827909629, 1836816527⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_99 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 99 = ⟨1303248187, 75374765⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102 = ⟨1516486685, 2082671253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51]
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

theorem power_118 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118 = ⟨2029146254, 280154270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59]
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

theorem power_134 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 134 = ⟨445214781, 1346295538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_140 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 140 = ⟨166789141, 776909418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_142 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 142 = ⟨2045471800, 21567742⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_150 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 150 = ⟨141696057, 732771971⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 152 = ⟨186674930, 98941776⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76]
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

theorem power_166 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 166 = ⟨1545644833, 1423557268⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_172 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 172 = ⟨1271351363, 2142894890⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_174 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 174 = ⟨1566056996, 1745888105⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 176 = ⟨1326093758, 824702110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_182 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 182 = ⟨2049618010, 1067206337⟩ := by
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

theorem power_192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 192 = ⟨1343082982, 1656388718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_198 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 198 = ⟨1388304776, 536803269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_204 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 204 = ⟨349974108, 1382066042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_206 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 206 = ⟨891793723, 1417325858⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103]
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

theorem power_224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 224 = ⟨1497340852, 2054439268⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_230 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 230 = ⟨1382570788, 293157249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_236 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 236 = ⟨1882349838, 1929949081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_238 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 238 = ⟨1707325511, 1098406816⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 240 = ⟨545370846, 562844461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_246 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 246 = ⟨1542475593, 236234992⟩ := by
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

theorem power_268 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 268 = ⟨2013245287, 307235301⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_134]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 280 = ⟨1151293179, 2142156513⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_140]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_284 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 284 = ⟨23079860, 1037577460⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_142]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_300 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 300 = ⟨1826511843, 427717874⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_150]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 304 = ⟨1931014169, 1213553800⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_152]
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

theorem power_332 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 332 = ⟨1776824621, 1228552608⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_166]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 344 = ⟨920191220, 656982226⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_172]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_348 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 348 = ⟨1388299958, 1206426289⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_174]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 352 = ⟨2122028404, 1461483964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_364 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 364 = ⟨658152473, 1072395370⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_182]
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

theorem power_384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 384 = ⟨1594705154, 1156423391⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_396 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 396 = ⟨1317899525, 1413993072⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_198]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 408 = ⟨869725335, 1982977009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_204]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_412 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 412 = ⟨2105482584, 779799999⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_206]
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

theorem power_448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 448 = ⟨1326191972, 1554410474⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_460 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 460 = ⟨1702972884, 206156245⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_230]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 472 = ⟨1631040737, 1802692420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_236]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_476 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 476 = ⟨795892619, 307427987⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_238]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 480 = ⟨300788412, 2003762236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_492 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 492 = ⟨1391406444, 1044822016⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_246]
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

theorem power_536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 536 = ⟨868141221, 1752893379⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_268]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 560 = ⟨1279482299, 2145341211⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 568 = ⟨1827897087, 929922642⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_284]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 600 = ⟨1183830334, 1283287492⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_300]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 608 = ⟨112946548, 968926260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_304]
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

theorem power_664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 664 = ⟨1497739154, 867480608⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_332]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 688 = ⟨1246945925, 1128446404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 696 = ⟨1453440674, 589119313⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_348]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 704 = ⟨1130890301, 1314091057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 728 = ⟨152082636, 622063853⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_364]
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

theorem power_768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 768 = ⟨784830374, 912241638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 792 = ⟨1120617728, 1601145033⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_396]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 816 = ⟨709216745, 661921156⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 824 = ⟨393192345, 1269883945⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_412]
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

theorem power_896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 896 = ⟨1475671350, 739745329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 920 = ⟨1067422211, 221235944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_460]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 944 = ⟨144926793, 2141311607⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 952 = ⟨736233126, 745912594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_476]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 960 = ⟨418523497, 1921984699⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 984 = ⟨2061938011, 1225693194⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_492]
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

theorem power_1072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1072 = ⟨171097394, 1990602842⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1120 = ⟨428562734, 499127922⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1136 = ⟨934113032, 310511167⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1200 = ⟨2053141228, 12472555⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1216 = ⟨222118537, 1014253609⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_608]
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

theorem power_1328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1328 = ⟨1052768950, 700500903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1376 = ⟨1771456860, 1392465920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1392 = ⟨1354106400, 443181508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1408 = ⟨105012991, 261334420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1456 = ⟨447640678, 314692891⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_728]
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

theorem power_1536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1536 = ⟨999230472, 1852479283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1584 = ⟨1189594089, 370965434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1632 = ⟨1906266428, 2062433102⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1648 = ⟨319382324, 289573192⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_824]
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

theorem power_1792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1792 = ⟨344093444, 1723950257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1840 = ⟨423791970, 467357182⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1888 = ⟨269305067, 1242485321⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1904 = ⟨547307125, 463271940⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1920 = ⟨203869561, 313423390⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1968 = ⟨1305669901, 1881194309⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_984]
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

theorem power_2144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2144 = ⟨945143520, 979357515⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2240 = ⟨1882985882, 1884234849⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2272 = ⟨308268370, 2093673186⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2400 = ⟨321804958, 211969623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2432 = ⟨1676081227, 1135991864⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1216]
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

theorem power_2656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2656 = ⟨800991336, 1543881133⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2752 = ⟨937276350, 1889866233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2784 = ⟨1360272642, 462407257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2816 = ⟨638925477, 1200786367⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2912 = ⟨1514720099, 1344022831⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1456]
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

theorem power_3072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3072 = ⟨2054061671, 949045631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3168 = ⟨1868814331, 1048694373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3264 = ⟨1045835668, 1112919339⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3296 = ⟨903616870, 1432862237⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1648]
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

theorem power_3584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3584 = ⟨1309393381, 53742718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3680 = ⟨993162928, 1170744481⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3776 = ⟨1759380646, 1693051226⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3808 = ⟨1506184608, 1755829396⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3840 = ⟨2080156404, 1988869649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3936 = ⟨993869978, 1660964583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1968]
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

theorem power_4288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4288 = ⟨1337526504, 177086970⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4480 = ⟨148358476, 1302044281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4544 = ⟨609701741, 767315046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4800 = ⟨1333172839, 2105072738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4864 = ⟨1327275430, 1972188598⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2432]
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

theorem power_5312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5312 = ⟨85906648, 1487213051⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5504 = ⟨558010101, 1952904556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5568 = ⟨99211207, 1946280920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5632 = ⟨1739299167, 1982296282⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5824 = ⟨1240031076, 1183521928⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2912]
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

theorem power_6144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6144 = ⟨1121167, 714917308⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6336 = ⟨445780260, 1075905986⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6528 = ⟨491178846, 571176726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6592 = ⟨2029889606, 1568983310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3296]
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

theorem power_7168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7168 = ⟨1883166840, 347102028⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7360 = ⟨508470430, 979783914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7552 = ⟨198166676, 739745441⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7616 = ⟨1101130210, 28496752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7680 = ⟨1699022782, 2146531477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7872 = ⟨1647829762, 864777955⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3936]
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

theorem power_8576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8576 = ⟨42830196, 2016881506⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8960 = ⟨2091181541, 1615031214⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9088 = ⟨236427592, 1624003215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9600 = ⟨1859245018, 579400817⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9728 = ⟨76857669, 1277280684⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4864]
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

theorem power_10624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10624 = ⟨127257755, 138520870⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11008 = ⟨1905939861, 629388659⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11136 = ⟨147298690, 1099763101⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11264 = ⟨226985029, 1154128883⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11648 = ⟨1954706102, 753082980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5824]
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

theorem power_12288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12288 = ⟨1475016787, 1876816901⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12672 = ⟨1198757226, 2146773352⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13056 = ⟨1464918947, 1524839126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13184 = ⟨917179047, 586675057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6592]
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

theorem power_14336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14336 = ⟨1731306458, 1551812567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14720 = ⟨312458750, 1882679726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15104 = ⟨1798126249, 1236021248⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15232 = ⟨1395708858, 1497177230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15360 = ⟨1368263916, 2076980552⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15744 = ⟨1326215179, 1403584070⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7872]
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

theorem power_17152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17152 = ⟨121948857, 1429064166⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17920 = ⟨1517789543, 430872700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18176 = ⟨277390402, 1017102786⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19200 = ⟨577643380, 209794086⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19456 = ⟨1672882969, 1149947594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9728]
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

theorem power_21248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21248 = ⟨349237010, 541976007⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22016 = ⟨90637269, 952277332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22272 = ⟨1233494247, 815501048⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22528 = ⟨286695904, 1021278776⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23296 = ⟨479665279, 2094867031⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11648]
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

theorem power_24577 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24577 = ⟨1524818422, 1781099582⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25344 = ⟨279340041, 1266969425⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26112 = ⟨733299889, 1597634788⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26368 = ⟨231300344, 22616870⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13184]
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

theorem power_28672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28672 = ⟨1124768046, 299494314⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29440 = ⟨309688732, 1590447564⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30208 = ⟨422667070, 645353689⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30464 = ⟨1306202290, 656337007⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30720 = ⟨1155186462, 790771269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31488 = ⟨1506146295, 15201801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15744]
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

theorem power_34304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34304 = ⟨1651788202, 1051285238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35840 = ⟨1055573105, 1574974366⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36352 = ⟨1666103267, 543807372⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38400 = ⟨733453396, 414961443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38912 = ⟨1693740220, 848695353⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19456]
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

theorem power_42496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42496 = ⟨1607105031, 64991137⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44032 = ⟨1331567834, 835563095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44544 = ⟨2059734770, 1626927132⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45056 = ⟨1984370174, 548484416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46592 = ⟨1589750714, 89434798⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23296]
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

theorem power_49154 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49154 = ⟨1822814362, 605789304⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24577]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50688 = ⟨165344061, 601375750⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52224 = ⟨1934269047, 1171518634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52736 = ⟨559851472, 639516914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26368]
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

theorem power_57345 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57345 = ⟨1225717054, 1595753655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58880 = ⟨705468968, 307830817⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60416 = ⟨173326764, 1317620144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60928 = ⟨704349578, 1737110009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61440 = ⟨1168068815, 1631133982⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62976 = ⟨513154727, 1233224454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31488]
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

theorem power_68608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 68608 = ⟨368688812, 1406464750⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71680 = ⟨545041803, 1880690526⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72704 = ⟨1659670602, 561643989⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76800 = ⟨1291436019, 379698066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77824 = ⟨1214106985, 780900129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38912]
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

theorem power_84992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84992 = ⟨231535418, 394352870⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88064 = ⟨1629336806, 1209471979⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89088 = ⟨1042833731, 101065615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90113 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90113 = ⟨958199570, 1802323799⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_93184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93184 = ⟨2140616907, 88929576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46592]
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

theorem power_98308 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98308 = ⟨700183440, 1721071448⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49154]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_101376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101376 = ⟨1803958918, 1911609679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104448 = ⟨2007972020, 427573065⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105472 = ⟨652753676, 326975263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52736]
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

theorem power_114690 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114690 = ⟨114661628, 1716202468⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57345]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_117760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117760 = ⟨2093537614, 1504172109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120832 = ⟨947160035, 834918877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121856 = ⟨1209236572, 1025248382⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122881 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122881 = ⟨536777494, 1335076259⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125952 = ⟨895303357, 1473739262⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62976]
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

theorem power_137216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 137216 = ⟨1757625041, 2055518664⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_143360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 143360 = ⟨957870942, 905094216⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_145408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 145408 = ⟨477007636, 1158627154⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_153600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 153600 = ⟨1507456974, 2049594119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_155649 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 155649 = ⟨24869872, 1272011871⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77824]
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

theorem power_169984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 169984 = ⟨1644701032, 1157789670⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_176128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 176128 = ⟨591304555, 68989614⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_178176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 178176 = ⟨942015741, 884128330⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_180226 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 180226 = ⟨801054651, 871226445⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90113]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_186368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 186368 = ⟨1787064488, 51350066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_188417 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 188417 = ⟨506062256, 475713267⟩ := by
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

theorem power_196616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 196616 = ⟨1399609862, 1982617235⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98308]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_202752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 202752 = ⟨1610082685, 851242621⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_208896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 208896 = ⟨891287480, 1172290213⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_210944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 210944 = ⟨1583620585, 920603234⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_219136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 219136 = ⟨232802090, 2145208109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_221185 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 221185 = ⟨1271347142, 17095735⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110592]
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

theorem power_229380 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 229380 = ⟨2118337965, 1819384752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114690]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_235520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 235520 = ⟨402089960, 1847126256⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_241664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 241664 = ⟨1696657789, 2121958423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_243712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 243712 = ⟨894328797, 399061936⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_245762 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 245762 = ⟨542318309, 248887067⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122881]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_251904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 251904 = ⟨2044929748, 722179404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_253953 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 253953 = ⟨28077064, 2130533930⟩ := by
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

theorem power_274432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 274432 = ⟨458199028, 2319221⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_137216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_286721 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 286721 = ⟨304113158, 1378493651⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_143360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_290816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 290816 = ⟨1458581325, 1279621404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_145408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_307200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 307200 = ⟨207319829, 330698049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_153600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_311298 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 311298 = ⟨1766444063, 1515981505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_155649]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_319489 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 319489 = ⟨1838888449, 1338159144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_159744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_323584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 323584 = ⟨655623719, 353143806⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_161792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_339968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 339968 = ⟨236415000, 1220441885⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_169984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_352257 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 352257 = ⟨34214817, 191411550⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_176128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_356352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 356352 = ⟨128738146, 457848703⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_178176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_360452 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 360452 = ⟨831559309, 545144803⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_180226]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_372736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 372736 = ⟨787391422, 234435571⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_186368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_376834 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 376834 = ⟨1327502529, 1045327121⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_188417]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_385025 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 385025 = ⟨180693516, 1222492645⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_192512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_389120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 389120 = ⟨875099799, 1659345298⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_194560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_393232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 393232 = ⟨1580085559, 788855863⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_196616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_405504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 405504 = ⟨1681738638, 1038838871⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_202752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_417793 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 417793 = ⟨657321348, 173001670⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_208896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_421888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 421888 = ⟨1212320872, 1495300507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_210944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_438272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 438272 = ⟨1167250594, 1854887903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_219136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_442370 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 442370 = ⟨1705947422, 1121658148⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_221185]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_450561 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 450561 = ⟨665030651, 1357185612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_225280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_454656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 454656 = ⟨1775957340, 1042791219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_227328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_458760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 458760 = ⟨673355490, 1670050658⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_229380]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_471040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 471040 = ⟨1085445012, 1626464664⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_235520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_483329 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 483329 = ⟨967314379, 285442223⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_241664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_487424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 487424 = ⟨1300871249, 1490001285⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_243712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_491524 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 491524 = ⟨683965578, 608438830⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_245762]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_503808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 503808 = ⟨2077839401, 709133143⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_251904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_507906 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 507906 = ⟨1354282084, 386623329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_253953]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_516097 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 516097 = ⟨523847539, 1349616237⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_258048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_520192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 520192 = ⟨1309629376, 2080668066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_260096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_548865 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 548865 = ⟨1922823721, 1196722759⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_274432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_573442 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 573442 = ⟨158587409, 1733775436⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_286721]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_581633 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 581633 = ⟨874631639, 316184562⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_290816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_614401 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 614401 = ⟨156903080, 1849887904⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_307200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_622596 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 622596 = ⟨571822688, 472343953⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_311298]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_638978 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 638978 = ⟨1357578335, 719274789⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_319489]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_647169 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 647169 = ⟨216751631, 645359366⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_323584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_679937 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 679937 = ⟨394826332, 539628558⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_339968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_704514 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 704514 = ⟨473643345, 139797955⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_352257]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_712705 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 712705 = ⟨727877909, 1593551288⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_356352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_720904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 720904 = ⟨146129024, 477787511⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_360452]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_745473 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 745473 = ⟨293193897, 1716126244⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_372736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_753668 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 753668 = ⟨28358227, 1116939694⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_376834]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_770050 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 770050 = ⟨1552932265, 1931375163⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_385025]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_778241 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 778241 = ⟨790003107, 717156990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_389120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_786464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 786464 = ⟨1158415754, 1772531664⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_393232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_811009 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 811009 = ⟨766380706, 303028759⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_405504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_835586 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 835586 = ⟨1099395725, 1602406076⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_417793]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_843777 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 843777 = ⟨2108824242, 1958090202⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_421888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_876545 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 876545 = ⟨1690232726, 1508622302⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_438272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_884740 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 884740 = ⟨2016557795, 65064928⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_442370]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_901122 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 901122 = ⟨1640348077, 1082504109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_450561]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_909313 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 909313 = ⟨90809265, 63098301⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_454656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_917520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 917520 = ⟨857116243, 453064100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_458760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_942081 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 942081 = ⟨1891599702, 669549217⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_471040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_966658 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 966658 = ⟨1978086448, 731966074⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_483329]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_974849 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 974849 = ⟨219998559, 1572029953⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_487424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_983048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 983048 = ⟨969141167, 281110246⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_491524]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1007617 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1007617 = ⟨1372325284, 1297847936⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_503808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1015812 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1015812 = ⟨59336233, 1657401022⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_507906]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1032194 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1032194 = ⟨227126220, 1578933761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_516097]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1040385 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1040385 = ⟨17670932, 1132412001⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_520192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1097730 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1097730 = ⟨1508818468, 9119783⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_548865]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1146884 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1146884 = ⟨796086604, 2045080163⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_573442]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1163266 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1163266 = ⟨1700039677, 1537625449⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_581633]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1228802 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1228802 = ⟨155874907, 1348260009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_614401]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1245192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1245192 = ⟨1319761567, 392519647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_622596]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1277956 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1277956 = ⟨52635222, 1842763118⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_638978]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1294338 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1294338 = ⟨1993191069, 1852724475⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_647169]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1359874 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1359874 = ⟨1132555968, 2077369405⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_679937]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1409028 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1409028 = ⟨1825202229, 1145156064⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_704514]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1425410 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1425410 = ⟨878704474, 1916017413⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_712705]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1441808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1441808 = ⟨212857926, 953034155⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_720904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1490946 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1490946 = ⟨47880568, 453337275⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_745473]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1507336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1507336 = ⟨872393584, 301987259⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_753668]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1540100 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1540100 = ⟨995447757, 1003829976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_770050]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1556482 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1556482 = ⟨33438720, 2031294485⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_778241]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1572928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1572928 = ⟨479939323, 2014263858⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_786464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1622018 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1622018 = ⟨1911338308, 859968653⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_811009]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1671172 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1671172 = ⟨2131231399, 589385662⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_835586]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1687554 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1687554 = ⟨1669263220, 1980176626⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_843777]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1753090 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1753090 = ⟨652666095, 530321719⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_876545]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1769480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1769480 = ⟨506187474, 2041231415⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_884740]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1802244 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1802244 = ⟨1597553539, 2000215266⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_901122]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1818626 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1818626 = ⟨875491507, 1824168612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_909313]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1835040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1835040 = ⟨1469077656, 603023⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_917520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1884162 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1884162 = ⟨1043169686, 2055167952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_942081]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1933316 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1933316 = ⟨196848653, 941967049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_966658]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1949698 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1949698 = ⟨297528927, 1575388432⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_974849]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1966096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1966096 = ⟨1531762388, 953711890⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_983048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2015234 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2015234 = ⟨1938463434, 1880643899⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1007617]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2031624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2031624 = ⟨1837067694, 264203777⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1015812]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2064388 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2064388 = ⟨438397711, 61565331⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1032194]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2080770 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2080770 = ⟨1071211295, 2008765422⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1040385]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2195460 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2195460 = ⟨1051878796, 2114238952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1097730]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2293768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2293768 = ⟨996183119, 200324074⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1146884]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2326532 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2326532 = ⟨966310297, 1992854641⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1163266]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2457604 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2457604 = ⟨335630493, 1102492012⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1228802]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2490384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2490384 = ⟨1069021699, 2036160946⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1245192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2555912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2555912 = ⟨178956461, 1658088682⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1277956]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2588676 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2588676 = ⟨295739770, 970310465⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1294338]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2719748 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2719748 = ⟨1644635556, 1215246150⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1359874]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2818056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2818056 = ⟨411376277, 841111775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1409028]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2850820 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2850820 = ⟨1383209247, 1274165810⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1425410]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2883616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2883616 = ⟨1679222176, 462906643⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1441808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2981892 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2981892 = ⟨954328253, 1851435890⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1490946]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3014672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3014672 = ⟨1646074005, 1298707839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1507336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3080200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3080200 = ⟨908257430, 1922082233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1540100]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3112964 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3112964 = ⟨1009771467, 1790646697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1556482]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3145856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3145856 = ⟨546930332, 1505165579⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1572928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3244036 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3244036 = ⟨1178451891, 1700826634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1622018]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3342344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3342344 = ⟨890363242, 542081472⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1671172]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3375108 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3375108 = ⟨922831281, 683116921⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1687554]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3506180 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3506180 = ⟨1409457949, 1511837914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1753090]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3538960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3538960 = ⟨1098807400, 1550060662⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1769480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3604488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3604488 = ⟨654174473, 656822844⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1802244]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3637252 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3637252 = ⟨1607771105, 2055151112⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1818626]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3670080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3670080 = ⟨723479276, 290201767⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1835040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3768324 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3768324 = ⟨756110133, 1375102505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1884162]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3866632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3866632 = ⟨1533385416, 81286255⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1933316]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3899396 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3899396 = ⟨2053606651, 1877309569⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1949698]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3932192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3932192 = ⟨1988959819, 2003914634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1966096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4030468 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4030468 = ⟨1196857147, 834818320⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2015234]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4063248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4063248 = ⟨379211737, 97895825⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2031624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4128776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4128776 = ⟨804408880, 1304219299⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2064388]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4161540 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4161540 = ⟨630249739, 1194819291⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2080770]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4390920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4390920 = ⟨458956580, 1911570161⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2195460]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4587536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4587536 = ⟨459511065, 2045436802⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2293768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4653064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4653064 = ⟨1347580397, 1506362092⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2326532]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4915208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4915208 = ⟨192533242, 542871434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2457604]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4980768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4980768 = ⟨2086141220, 2091943806⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2490384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5111824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5111824 = ⟨1939219864, 1632570882⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2555912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5177352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5177352 = ⟨1771062584, 1115933733⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2588676]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5439496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5439496 = ⟨1596425778, 249898199⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2719748]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5636112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5636112 = ⟨747511347, 284419357⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2818056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5701640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5701640 = ⟨1717260106, 1919261683⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2850820]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5767232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5767232 = ⟨662101445, 981254839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2883616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5963784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5963784 = ⟨1405408427, 331156868⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2981892]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6029344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6029344 = ⟨1722136052, 257727727⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3014672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6160400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6160400 = ⟨1947953998, 1609436625⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3080200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6225928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6225928 = ⟨1729180899, 480882014⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3112964]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6291712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6291712 = ⟨986107101, 686343399⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3145856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6488072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6488072 = ⟨1791786300, 1895889158⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3244036]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6684688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6684688 = ⟨1126824827, 1579667289⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3342344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6750216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6750216 = ⟨477564784, 774088502⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3375108]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7012360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7012360 = ⟨1022948441, 2141692017⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3506180]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7077920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7077920 = ⟨1627992829, 1806495570⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3538960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7208976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7208976 = ⟨1335376053, 1960121109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3604488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7274504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7274504 = ⟨916365445, 408725859⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3637252]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7340160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7340160 = ⟨1353636408, 2105549725⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3670080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7536648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7536648 = ⟨870790052, 1802392273⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3768324]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7733264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7733264 = ⟨1632635382, 1746584218⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3866632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7798792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7798792 = ⟨1633054010, 697818744⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3899396]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7864384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7864384 = ⟨1744890576, 1045248944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3932192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8060936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8060936 = ⟨762962916, 963191295⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4030468]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8126496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8126496 = ⟨1945294550, 1960573798⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4063248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8257552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8257552 = ⟨959318581, 1965148613⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4128776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8323080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8323080 = ⟨986976185, 1644261514⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4161540]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8781840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8781840 = ⟨175431202, 14263648⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4390920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9175072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9175072 = ⟨1745934752, 1399754429⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4587536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9306128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9306128 = ⟨31240663, 999915089⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4653064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9830416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9830416 = ⟨913637553, 2090079737⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4915208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9961536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9961536 = ⟨1126549508, 391813918⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4980768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10223648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10223648 = ⟨403409883, 1308855806⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5111824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10354704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10354704 = ⟨1905074391, 386624921⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5177352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10878992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10878992 = ⟨413282901, 364563849⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5439496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11272224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11272224 = ⟨927768941, 450455606⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5636112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11403280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11403280 = ⟨34148810, 313870652⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5701640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11534464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11534464 = ⟨130625086, 1392003839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5767232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11927568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11927568 = ⟨1588345190, 1625854063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5963784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12058688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12058688 = ⟨542622250, 388922918⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6029344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12320800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12320800 = ⟨1367345218, 1958458284⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6160400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12451856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12451856 = ⟨471951725, 469527673⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6225928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12583424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12583424 = ⟨294955624, 43656284⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6291712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12976144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12976144 = ⟨1006581846, 29836157⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6488072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13369376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13369376 = ⟨324852805, 1848325649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6684688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13500432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13500432 = ⟨1120251134, 1703154131⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6750216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14024720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14024720 = ⟨1433018481, 418557419⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7012360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14155840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14155840 = ⟨1191411699, 2085790951⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7077920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14417952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14417952 = ⟨368875006, 501420243⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7208976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14549008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14549008 = ⟨2017608251, 318919078⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7274504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14680320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14680320 = ⟨570283969, 1280968064⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7340160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15073296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15073296 = ⟨1390231461, 749167785⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7536648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15466528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15466528 = ⟨1614639890, 1739035793⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7733264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15597584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15597584 = ⟨523194902, 1411733149⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7798792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15728768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15728768 = ⟨1472515367, 1407001491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7864384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16121872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16121872 = ⟨1629263548, 661130065⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8060936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16252992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16252992 = ⟨466961221, 1822787161⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8126496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16515104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16515104 = ⟨1040089406, 1228098109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8257552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16646160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16646160 = ⟨1959887496, 401268298⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8323080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17563680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17563680 = ⟨1892897753, 331742406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8781840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18350144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18350144 = ⟨54005688, 662205835⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9175072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18612256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18612256 = ⟨640934840, 460462406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9306128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19660832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19660832 = ⟨1240153042, 1348539629⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9830416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19923072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19923072 = ⟨1364177205, 1885363377⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9961536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20447296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20447296 = ⟨1266402730, 1198140650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10223648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20709408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20709408 = ⟨1200651342, 101012865⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10354704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21757984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21757984 = ⟨1684922687, 1075257340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10878992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22544448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22544448 = ⟨1489805829, 2105124206⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11272224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22806560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22806560 = ⟨1391556908, 815913899⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11403280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23068928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23068928 = ⟨341780619, 733867894⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11534464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23855136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23855136 = ⟨938008920, 1915150981⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11927568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24117376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24117376 = ⟨670537799, 1543374098⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12058688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24641600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24641600 = ⟨1951495951, 78281358⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12320800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24903712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24903712 = ⟨1868988033, 1634643136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12451856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25166848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25166848 = ⟨405858396, 413054922⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12583424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25952288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25952288 = ⟨263324523, 1914229172⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12976144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26738752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26738752 = ⟨538508982, 734333568⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13369376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27000864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27000864 = ⟨491695970, 246326787⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13500432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28049440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28049440 = ⟨1230993897, 1738536711⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14024720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28311680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28311680 = ⟨1645593957, 232700903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14155840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28835904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28835904 = ⟨661714772, 1742173782⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14417952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29098016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29098016 = ⟨1897246760, 1383809451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14549008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29360640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29360640 = ⟨1756181584, 1552321304⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14680320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30146592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30146592 = ⟨951267492, 1022216002⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15073296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30933056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30933056 = ⟨626192062, 1275334486⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15466528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31195168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31195168 = ⟨872296009, 1586349128⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15597584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31457536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31457536 = ⟨211575503, 242533175⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15728768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32243744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32243744 = ⟨656173519, 1704384115⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16121872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32505984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32505984 = ⟨756619415, 988209085⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16252992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33030208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33030208 = ⟨1151086712, 1335716271⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16515104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33292320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33292320 = ⟨511113095, 600528204⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16646160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35127360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35127360 = ⟨759118631, 2026811563⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17563680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36700288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36700288 = ⟨1662491411, 196835947⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18350144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37224512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37224512 = ⟨1653436667, 924612661⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18612256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39321664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39321664 = ⟨544010650, 283098701⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19660832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39846144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39846144 = ⟨772720059, 236390069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19923072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40894592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40894592 = ⟨620572780, 1530549257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20447296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41418816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41418816 = ⟨4008325, 468751657⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20709408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43515968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43515968 = ⟨960739213, 851763445⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21757984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45088896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45088896 = ⟨406451210, 1367876393⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22544448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45613120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45613120 = ⟨132355254, 474482638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22806560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46137856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46137856 = ⟨833060292, 311905950⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23068928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47710272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47710272 = ⟨1016016691, 1873956605⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23855136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48234752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48234752 = ⟨1143097044, 723181136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24117376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49283200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49283200 = ⟨555851019, 1346457398⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24641600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49807424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49807424 = ⟨411477238, 1982797335⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24903712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51904576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51904576 = ⟨428391982, 1207218365⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25952288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53477504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53477504 = ⟨255089472, 1257540438⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26738752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54001728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54001728 = ⟨623506101, 1664902299⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27000864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56098880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56098880 = ⟨35031212, 615732569⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28049440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56623360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56623360 = ⟨870311839, 68784605⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28311680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57671808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57671808 = ⟨2033507314, 1795044071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28835904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58196032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58196032 = ⟨660515303, 245053659⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29098016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58721280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58721280 = ⟨685109443, 308131929⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29360640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60293184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60293184 = ⟨1332174066, 2007413313⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30146592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61866112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61866112 = ⟨243267978, 1039631690⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30933056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62390336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62390336 = ⟨414297317, 1528057982⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31195168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62915072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62915072 = ⟨2001889776, 1546323577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31457536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64487488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64487488 = ⟨1575852114, 924199066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32243744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65011968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65011968 = ⟨1803331212, 347787032⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32505984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66060416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66060416 = ⟨6804651, 1171669079⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33030208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66584640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66584640 = ⟨370407316, 572946297⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33292320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_70254720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70254720 = ⟨1639393672, 2080068976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35127360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73400576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73400576 = ⟨1948325705, 393614093⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36700288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_74449024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 74449024 = ⟨1014468297, 1312914434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37224512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_78643328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 78643328 = ⟨206851156, 1795327758⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39321664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_79692288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79692288 = ⟨2071981270, 1474702289⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39846144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_81789184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81789184 = ⟨1386355515, 792591991⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40894592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_82837632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 82837632 = ⟨540801188, 761713160⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41418816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87031936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87031936 = ⟨1980673514, 1848189938⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43515968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90177792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90177792 = ⟨1935264840, 1489488006⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45088896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_91226240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 91226240 = ⟨189191315, 507624181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45613120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92275712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92275712 = ⟨1569205000, 1460088186⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46137856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_95420544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 95420544 = ⟨279527720, 979594660⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47710272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_96469504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96469504 = ⟨1348085757, 1362597551⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48234752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98566400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98566400 = ⟨2004859019, 37543447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49283200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_99614848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 99614848 = ⟨17715140, 338311090⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49807424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_103809152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103809152 = ⟨1048615237, 1640850111⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51904576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106955008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106955008 = ⟨1755960729, 370372920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53477504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108003456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108003456 = ⟨29230097, 1122059357⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54001728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_112197760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112197760 = ⟨1830803352, 1814545991⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56098880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_113246720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 113246720 = ⟨254841340, 1834532528⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56623360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115343616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115343616 = ⟨471592156, 170421558⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57671808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_116392064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116392064 = ⟨1225099255, 1359082145⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58196032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120586368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120586368 = ⟨1937341932, 705215736⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60293184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123732224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123732224 = ⟨1201437145, 899397049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61866112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124780672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124780672 = ⟨2086942878, 1340197334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62390336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125830144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125830144 = ⟨832857621, 1800803482⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62915072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_128974976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128974976 = ⟨1992616259, 2087032529⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64487488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_130023936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 130023936 = ⟨1283029195, 1123439711⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65011968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_132120832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 132120832 = ⟨613154020, 1832737049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66060416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_133169280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 133169280 = ⟨1181457295, 1254326912⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66584640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_140509440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 140509440 = ⟨59437718, 2144626587⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70254720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_146801152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 146801152 = ⟨681077543, 1957648220⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73400576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_148898048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 148898048 = ⟨1176780466, 204638144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74449024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_157286656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 157286656 = ⟨505676487, 1067867507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78643328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_159384576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 159384576 = ⟨1697594322, 1318496168⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79692288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_163578368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 163578368 = ⟨1976827794, 1641774056⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81789184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_165675264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 165675264 = ⟨711492341, 1228574320⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82837632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_174063872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 174063872 = ⟨1094867061, 1333258505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87031936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_180355584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 180355584 = ⟨168615074, 1227221221⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90177792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_182452480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 182452480 = ⟨667697223, 1853048291⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91226240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_190841088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 190841088 = ⟨857803951, 242929832⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_95420544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_192939008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 192939008 = ⟨1831338762, 818744620⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96469504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_197132800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 197132800 = ⟨285486106, 777642281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98566400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_199229696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 199229696 = ⟨882479568, 1792167884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99614848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_207618304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 207618304 = ⟨1452360845, 1531119005⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103809152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_213910016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 213910016 = ⟨933077954, 1571729903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106955008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_216006912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 216006912 = ⟨1453667977, 569119342⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108003456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_224395520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 224395520 = ⟨1926355637, 1910653852⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112197760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_226493440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 226493440 = ⟨924436841, 179213100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_113246720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_230687232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 230687232 = ⟨1869952398, 1555129149⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115343616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_232784128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 232784128 = ⟨1057587015, 140458414⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116392064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_241172736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 241172736 = ⟨1852450377, 1190008839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120586368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_247464448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 247464448 = ⟨17719502, 1731642582⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123732224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_249561344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 249561344 = ⟨565181278, 2104840877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124780672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_257949952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 257949952 = ⟨1789823249, 211250683⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128974976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_260047872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 260047872 = ⟨1026246497, 462715637⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_130023936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_264241664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 264241664 = ⟨129107154, 1681350538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_132120832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_266338560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 266338560 = ⟨94178552, 800478803⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133169280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_281018880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 281018880 = ⟨1734480942, 1023013125⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_140509440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_293602304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 293602304 = ⟨1343434959, 1740046445⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_146801152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_297796096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 297796096 = ⟨1605682483, 727970777⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_148898048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_314573312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 314573312 = ⟨1714504766, 1751965935⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_157286656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_327156736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 327156736 = ⟨1418607411, 1674242439⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_163578368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_331350528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 331350528 = ⟨943018877, 1313105112⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_165675264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_348127744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 348127744 = ⟨206852966, 528309350⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_174063872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_360711168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 360711168 = ⟨742503567, 20511103⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_180355584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_364904960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 364904960 = ⟨1599512977, 928579805⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_182452480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_381682176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 381682176 = ⟨676756617, 375021096⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_190841088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_394265600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 394265600 = ⟨1029184762, 1463990705⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_197132800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_398459392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 398459392 = ⟨1721077615, 1841952380⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_199229696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_415236608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 415236608 = ⟨1631722823, 1981467670⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_207618304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_427820032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 427820032 = ⟨1908257733, 904587623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_213910016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_432013824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 432013824 = ⟨1035851695, 1043000327⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_216006912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_448791040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 448791040 = ⟨1657000754, 102874905⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_224395520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_461374464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 461374464 = ⟨136027637, 84984741⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_230687232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_465568256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 465568256 = ⟨111263582, 1518837077⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_232784128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_482345472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 482345472 = ⟨718869836, 118924817⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_241172736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_494928896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 494928896 = ⟨776651208, 1692488596⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_247464448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_499122688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 499122688 = ⟨1281772582, 383216956⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_249561344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_515899904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 515899904 = ⟨315779141, 839149096⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_257949952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_528483328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 528483328 = ⟨1630230719, 432660073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_264241664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_532677120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 532677120 = ⟨841903081, 761027717⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_266338560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_562037760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 562037760 = ⟨413054922, 1741625251⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_281018880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_595592192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 595592192 = ⟨308131929, 1462374204⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_297796096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_629146624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 629146624 = ⟨1460088186, 578278647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_314573312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_662701056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 662701056 = ⟨1800803482, 1314626026⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_331350528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_696255488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 696255488 = ⟨1318496168, 449889325⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_348127744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_729809920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 729809920 = ⟨818744620, 316144885⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_364904960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_763364352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 763364352 = ⟨179213100, 1223046806⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_381682176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_796918784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 796918784 = ⟨462715637, 1121237150⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_398459392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_830473216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 830473216 = ⟨1740046445, 804048688⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_415236608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_864027648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 864027648 = ⟨1674242439, 728876236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_432013824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_897582080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 897582080 = ⟨20511103, 1404980080⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_448791040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_931136512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 931136512 = ⟨1463990705, 1118298885⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_465568256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_964690944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 964690944 = ⟨904587623, 239225914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_482345472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_998245376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 998245376 = ⟨84984741, 2011456010⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_499122688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1031799808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1031799808 = ⟨1692488596, 1370832439⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_515899904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1065354240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1065354240 = ⟨432660073, 517252928⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_532677120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 96) = ⟨405858396, 413054922⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 96 = 25166848 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_25166848

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨405858396, 413054922⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 96) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 97) = ⟨413054922, 1741625251⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 97 = 562037760 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_562037760

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨413054922, 1741625251⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 97) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 98) = ⟨1343434959, 1740046445⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 98 = 293602304 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_293602304

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1343434959, 1740046445⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 98) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 99) = ⟨1740046445, 804048688⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 99 = 830473216 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_830473216

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1740046445, 804048688⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 99) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 100) = ⟨1697594322, 1318496168⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 100 = 159384576 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_159384576

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1697594322, 1318496168⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 100) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 101) = ⟨1318496168, 449889325⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 101 = 696255488 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_696255488

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1318496168, 449889325⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 101) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 102) = ⟨1908257733, 904587623⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 102 = 427820032 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_427820032

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1908257733, 904587623⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 102) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 103) = ⟨904587623, 239225914⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 103 = 964690944 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_964690944

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨904587623, 239225914⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 103) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 104) = ⟨1569205000, 1460088186⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 104 = 92275712 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_92275712

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1569205000, 1460088186⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 104) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 105) = ⟨1460088186, 578278647⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 105 = 629146624 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_629146624

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1460088186, 578278647⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 105) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 106) = ⟨742503567, 20511103⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 106 = 360711168 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_360711168

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨742503567, 20511103⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 106) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 107) = ⟨20511103, 1404980080⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 107 = 897582080 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_897582080

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨20511103, 1404980080⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 107) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 108) = ⟨924436841, 179213100⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 108 = 226493440 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_226493440

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨924436841, 179213100⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 108) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 109) = ⟨179213100, 1223046806⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 109 = 763364352 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_763364352

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨179213100, 1223046806⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 109) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 110) = ⟨776651208, 1692488596⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 110 = 494928896 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_494928896

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨776651208, 1692488596⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 110) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 111) = ⟨1692488596, 1370832439⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 111 = 1031799808 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1031799808

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1692488596, 1370832439⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 111) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 112) = ⟨685109443, 308131929⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 112 = 58721280 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_58721280

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨685109443, 308131929⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 112) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 113) = ⟨308131929, 1462374204⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 113 = 595592192 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_595592192

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨308131929, 1462374204⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 113) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 114) = ⟨1418607411, 1674242439⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 114 = 327156736 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_327156736

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1418607411, 1674242439⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 114) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 115) = ⟨1674242439, 728876236⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 115 = 864027648 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_864027648

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1674242439, 728876236⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 115) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 116) = ⟨1831338762, 818744620⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 116 = 192939008 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_192939008

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1831338762, 818744620⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 116) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 117) = ⟨818744620, 316144885⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 117 = 729809920 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_729809920

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨818744620, 316144885⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 117) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 118) = ⟨136027637, 84984741⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 118 = 461374464 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_461374464

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨136027637, 84984741⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 118) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 119) = ⟨84984741, 2011456010⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 119 = 998245376 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_998245376

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨84984741, 2011456010⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 119) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 120) = ⟨832857621, 1800803482⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 120 = 125830144 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_125830144

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨832857621, 1800803482⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 120) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 121) = ⟨1800803482, 1314626026⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 121 = 662701056 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_662701056

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1800803482, 1314626026⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 121) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 122) = ⟨1029184762, 1463990705⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 122 = 394265600 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_394265600

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1029184762, 1463990705⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 122) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 123) = ⟨1463990705, 1118298885⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 123 = 931136512 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_931136512

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1463990705, 1118298885⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 123) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 124) = ⟨1026246497, 462715637⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 124 = 260047872 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_260047872

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1026246497, 462715637⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 124) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 125) = ⟨462715637, 1121237150⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 125 = 796918784 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_796918784

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨462715637, 1121237150⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 125) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 126) = ⟨1630230719, 432660073⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 126 = 528483328 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_528483328

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1630230719, 432660073⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 126) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 127) = ⟨432660073, 517252928⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 127 = 1065354240 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1065354240

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨432660073, 517252928⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 127) := by
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

end R17TableAChunk03Certificate
