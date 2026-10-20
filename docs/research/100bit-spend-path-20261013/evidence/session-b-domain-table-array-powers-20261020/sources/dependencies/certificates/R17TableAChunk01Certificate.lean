import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk01Certificate
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

theorem power_32 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32 = ⟨334835419, 1444967316⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16]
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

theorem power_64 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64 = ⟨2042371533, 1362265296⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32]
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

theorem power_96 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96 = ⟨1827909629, 1836816527⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48]
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

theorem power_112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112 = ⟨2110227055, 661472412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56]
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

theorem power_120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120 = ⟨1743886464, 1431800964⟩ := by
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

theorem power_128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128 = ⟨212706801, 1223819887⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_132 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 132 = ⟨198245992, 796735524⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 136 = ⟨1739793648, 871532832⟩ := by
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

theorem power_148 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 148 = ⟨1797069868, 1569931230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74]
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

theorem power_160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 160 = ⟨352777635, 313115116⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_164 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 164 = ⟨1808739933, 169886250⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 168 = ⟨502934906, 432562679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_172 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 172 = ⟨1271351363, 2142894890⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 176 = ⟨1326093758, 824702110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_180 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 180 = ⟨440283696, 1083008219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90]
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

theorem power_192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 192 = ⟨1343082982, 1656388718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96]
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

theorem power_204 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 204 = ⟨349974108, 1382066042⟩ := by
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

theorem power_224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 224 = ⟨1497340852, 2054439268⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_228 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 228 = ⟨470360473, 1771595164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 232 = ⟨1705761383, 185122675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_236 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 236 = ⟨1882349838, 1929949081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 240 = ⟨545370846, 562844461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_244 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 244 = ⟨840379230, 2035177650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122]
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

theorem power_256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 256 = ⟨421007138, 256177860⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 264 = ⟨768841324, 1818863266⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_132]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 272 = ⟨1106204247, 1950210306⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 280 = ⟨1151293179, 2142156513⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_140]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 288 = ⟨1178716014, 1579375203⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 296 = ⟨224965265, 159335170⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_148]
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

theorem power_320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 320 = ⟨1637047685, 109864373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 328 = ⟨926055753, 540139726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_164]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 336 = ⟨180537201, 1575865056⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 344 = ⟨920191220, 656982226⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_172]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 352 = ⟨2122028404, 1461483964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 360 = ⟨1022383927, 1626835633⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_180]
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

theorem power_384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 384 = ⟨1594705154, 1156423391⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 392 = ⟨396447072, 406060497⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_196]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 400 = ⟨1872990432, 1178172302⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 408 = ⟨869725335, 1982977009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_204]
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

theorem power_448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 448 = ⟨1326191972, 1554410474⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 456 = ⟨1050515860, 1972726217⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_228]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 464 = ⟨761225645, 1514363314⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 472 = ⟨1631040737, 1802692420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_236]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 480 = ⟨300788412, 2003762236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 488 = ⟨1001236781, 1044516446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_244]
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

theorem power_512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 512 = ⟨6346213, 905523693⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 528 = ⟨765837868, 957818106⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 544 = ⟨1192151435, 1028938634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 560 = ⟨1279482299, 2145341211⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 576 = ⟨1603309155, 1317339952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 592 = ⟨462102546, 1660293932⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_296]
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

theorem power_640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 640 = ⟨982766847, 1369509443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 656 = ⟨1195617483, 37201067⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 672 = ⟨1863904991, 681598711⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 688 = ⟨1246945925, 1128446404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 704 = ⟨1130890301, 1314091057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 720 = ⟨330499511, 1255545984⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_360]
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

theorem power_768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 768 = ⟨784830374, 912241638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 784 = ⟨1560235557, 1166001668⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 800 = ⟨1630963856, 82519081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 816 = ⟨709216745, 661921156⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_408]
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

theorem power_896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 896 = ⟨1475671350, 739745329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 912 = ⟨345462981, 482925972⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 928 = ⟨192925011, 1863974752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 944 = ⟨144926793, 2141311607⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 960 = ⟨418523497, 1921984699⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 976 = ⟨1625484020, 323681644⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_488]
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

theorem power_1024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1024 = ⟨1022251061, 788094511⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1056 = ⟨1351366012, 1794883792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1088 = ⟨1453585800, 1686756607⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1120 = ⟨428562734, 499127922⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1152 = ⟨2144756169, 1973977555⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1184 = ⟨1392219141, 868524623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_592]
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

theorem power_1280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1280 = ⟨1774187400, 1713497086⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1312 = ⟨1361133795, 1467941404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1344 = ⟨1447121614, 1053732556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1376 = ⟨1771456860, 1392465920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1408 = ⟨105012991, 261334420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1440 = ⟨1445302729, 1296213244⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_720]
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

theorem power_1536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1536 = ⟨999230472, 1852479283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1568 = ⟨1111694799, 881760195⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1600 = ⟨517742188, 968413651⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1632 = ⟨1906266428, 2062433102⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_816]
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

theorem power_1792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1792 = ⟨344093444, 1723950257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1824 = ⟨1157368979, 1934990557⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1856 = ⟨2162587, 1662102570⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1888 = ⟨269305067, 1242485321⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1920 = ⟨203869561, 313423390⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1952 = ⟨1871828618, 1847683492⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_976]
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

theorem power_2048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2048 = ⟨1633461177, 574296567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2112 = ⟨2063130879, 1272838818⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2176 = ⟨1655011431, 2085598907⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2240 = ⟨1882985882, 1884234849⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2304 = ⟨505774551, 1187398701⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2368 = ⟨39852141, 123936243⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1184]
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

theorem power_2560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2560 = ⟨1743980363, 345791924⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2624 = ⟨1221120023, 1584263814⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2688 = ⟨319360190, 618255967⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2752 = ⟨937276350, 1889866233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2816 = ⟨638925477, 1200786367⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2880 = ⟨2050207099, 979596272⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1440]
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

theorem power_3072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3072 = ⟨2054061671, 949045631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3136 = ⟨2017447582, 2138555804⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3200 = ⟨1230785717, 932947748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3264 = ⟨1045835668, 1112919339⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1632]
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

theorem power_3584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3584 = ⟨1309393381, 53742718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3648 = ⟨2120725548, 846203964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3712 = ⟨1273782452, 924138332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3776 = ⟨1759380646, 1693051226⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3840 = ⟨2080156404, 1988869649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3904 = ⟨314388810, 1013513450⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1952]
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

theorem power_4096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4096 = ⟨595037635, 2111542451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4224 = ⟨1810308513, 779811684⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4352 = ⟨718921583, 1008587178⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4480 = ⟨148358476, 1302044281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4608 = ⟨1781794005, 336873408⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4736 = ⟨272617121, 579551580⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2368]
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

theorem power_5120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5120 = ⟨235158087, 2112924242⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5248 = ⟨1290866284, 1587498888⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5376 = ⟨967187167, 1461124768⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5504 = ⟨558010101, 1952904556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5632 = ⟨1739299167, 1982296282⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5760 = ⟨175645010, 1734378279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2880]
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

theorem power_6144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6144 = ⟨1121167, 714917308⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6272 = ⟨1392302454, 203859073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6400 = ⟨977208331, 1995798003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6528 = ⟨491178846, 571176726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3264]
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

theorem power_7168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7168 = ⟨1883166840, 347102028⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7296 = ⟨236244120, 866051848⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7424 = ⟨719349967, 2102971509⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7552 = ⟨198166676, 739745441⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7680 = ⟨1699022782, 2146531477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7808 = ⟨1996451271, 146269947⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3904]
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

theorem power_8192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8192 = ⟨1799120754, 343598868⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8448 = ⟨1508101166, 1752846715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8704 = ⟨252837685, 2006332926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8960 = ⟨2091181541, 1615031214⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9216 = ⟨1702571195, 1397706324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9472 = ⟨2016094574, 1147504298⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4736]
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

theorem power_10240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10240 = ⟨1242192167, 1322293366⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10496 = ⟨1825573200, 854560364⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10752 = ⟨133802874, 733650364⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11008 = ⟨1905939861, 629388659⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11264 = ⟨226985029, 1154128883⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11520 = ⟨1411573869, 756888130⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5760]
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

theorem power_12288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12288 = ⟨1475016787, 1876816901⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12544 = ⟨1303271673, 1211882786⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12800 = ⟨670508625, 2057653994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13056 = ⟨1464918947, 1524839126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6528]
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

theorem power_14336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14336 = ⟨1731306458, 1551812567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14592 = ⟨2040419523, 293774007⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14848 = ⟨520833839, 1618182004⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15104 = ⟨1798126249, 1236021248⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15360 = ⟨1368263916, 2076980552⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15616 = ⟨139198880, 1155184073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7808]
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

theorem power_16385 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16385 = ⟨3142946, 1225950837⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16896 = ⟨1864067894, 380717230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17408 = ⟨913684129, 1336358039⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17920 = ⟨1517789543, 430872700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18432 = ⟨1139757936, 161139962⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18944 = ⟨83021569, 1776986900⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9472]
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

theorem power_20480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20480 = ⟨433600440, 167145119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20992 = ⟨2108569002, 332819919⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21504 = ⟨1700714437, 566394792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22016 = ⟨90637269, 952277332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22528 = ⟨286695904, 1021278776⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23040 = ⟨512700922, 986405252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11520]
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

theorem power_24576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24576 = ⟨503318431, 730224775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25088 = ⟨354002285, 308304222⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25600 = ⟨1627995231, 271303573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26112 = ⟨733299889, 1597634788⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13056]
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

theorem power_28672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28672 = ⟨1124768046, 299494314⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29184 = ⟨212160839, 1626753054⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29696 = ⟨1800149012, 1373092732⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30208 = ⟨422667070, 645353689⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30720 = ⟨1155186462, 790771269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31232 = ⟨1863885482, 1326705008⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15616]
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

theorem power_32770 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32770 = ⟨1517049078, 1031039632⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16385]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33792 = ⟨2104985194, 631590980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34816 = ⟨1765678898, 2028236613⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35840 = ⟨1055573105, 1574974366⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36864 = ⟨1421883301, 1767600112⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37888 = ⟨451882769, 1853894340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18944]
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

theorem power_40960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40960 = ⟨263253631, 1948074535⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41984 = ⟨2071856540, 882531073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43008 = ⟨1503715524, 748528002⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44032 = ⟨1331567834, 835563095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45056 = ⟨1984370174, 548484416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46080 = ⟨2092093316, 989477899⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23040]
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

theorem power_49153 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49153 = ⟨550144080, 294583606⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50176 = ⟨1062485927, 1068122241⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51200 = ⟨687167191, 1193781868⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52224 = ⟨1934269047, 1171518634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53248 = ⟨528497962, 2048433423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54272 = ⟨1176403617, 782773078⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27136]
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

theorem power_57344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57344 = ⟨347749121, 1576860820⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58368 = ⟨287812835, 2081660990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59392 = ⟨1076514332, 1068664781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60416 = ⟨173326764, 1317620144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61440 = ⟨1168068815, 1631133982⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62464 = ⟨1733341057, 673759763⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31232]
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

theorem power_65540 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65540 = ⟨122035995, 33491108⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32770]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_67584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67584 = ⟨2016807951, 234018695⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69632 = ⟨1964662320, 1382435771⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71680 = ⟨545041803, 1880690526⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73728 = ⟨124482577, 226221110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_75776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 75776 = ⟨1210077794, 246102266⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37888]
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

theorem power_81921 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81921 = ⟨284080979, 1960175794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_83968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83968 = ⟨1235766230, 338243230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_86016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86016 = ⟨36975016, 821963373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88064 = ⟨1629336806, 1209471979⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90112 = ⟨338018326, 944583937⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92160 = ⟨713314261, 425545952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46080]
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

theorem power_98306 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98306 = ⟨1584872252, 144617744⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49153]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_100352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100352 = ⟨1300335129, 1837567123⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102400 = ⟨606906923, 1264738384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104448 = ⟨2007972020, 427573065⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106496 = ⟨1488671228, 939868393⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108544 = ⟨1032881673, 494228663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54272]
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

theorem power_114689 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114689 = ⟨485081585, 17595000⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_116736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116736 = ⟨342937346, 440901543⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_118784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118784 = ⟨845078094, 149898124⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120832 = ⟨947160035, 834918877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122880 = ⟨1829052821, 673049321⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124928 = ⟨346773666, 152947344⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62464]
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

theorem power_131080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131080 = ⟨32161107, 1640865651⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65540]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_135168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 135168 = ⟨798338207, 2110850421⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_139264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 139264 = ⟨521340221, 1824173925⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_143360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 143360 = ⟨957870942, 905094216⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_147457 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 147457 = ⟨158671062, 1058418546⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_151552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 151552 = ⟨2001642678, 1520422911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_155648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 155648 = ⟨940196297, 1361581394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_159744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 159744 = ⟨1924483244, 1528988896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_163842 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 163842 = ⟨1934070269, 1317681930⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81921]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_167936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 167936 = ⟨729011542, 952009042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_172032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 172032 = ⟨735504938, 198004457⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_176128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 176128 = ⟨591304555, 68989614⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_180225 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 180225 = ⟨281293941, 1865282473⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_184320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 184320 = ⟨1029245122, 1158447597⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92160]
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

theorem power_196612 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 196612 = ⟨1785235520, 429490843⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98306]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_200704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 200704 = ⟨1631496031, 481893475⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_204800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 204800 = ⟨607954189, 1091734815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_208896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 208896 = ⟨891287480, 1172290213⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_212993 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 212993 = ⟨797072793, 1008915408⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_217088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 217088 = ⟨1876139646, 119923533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_221184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 221184 = ⟨1212070390, 338345678⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_225280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 225280 = ⟨122809504, 181977862⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_229378 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 229378 = ⟨877553982, 2031144991⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114689]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_233472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 233472 = ⟨953139263, 265503960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_237568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 237568 = ⟨474711937, 1020011657⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_241664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 241664 = ⟨1696657789, 2121958423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_245761 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 245761 = ⟨295634633, 887773683⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_249856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 249856 = ⟨887385898, 608769478⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124928]
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

theorem power_262160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 262160 = ⟨462292150, 1877942832⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_270336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 270336 = ⟨844712212, 1454882131⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_135168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_278529 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 278529 = ⟨508181384, 1652912611⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_139264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_286720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 286720 = ⟨795729789, 119644040⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_143360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_294914 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 294914 = ⟨688532831, 1887069744⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_147457]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_303104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 303104 = ⟨1479292912, 403634516⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_151552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_311297 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 311297 = ⟨954517537, 501632887⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_155648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_319488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 319488 = ⟨1565145988, 1765289675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_159744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_327684 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 327684 = ⟨114470081, 488520796⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_163842]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_335872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 335872 = ⟨530115096, 90442098⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_167936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_344065 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 344065 = ⟨88683918, 1537419223⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_172032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_352256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 352256 = ⟨2049933380, 1834113202⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_176128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_360450 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 360450 = ⟨3403437, 585479487⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_180225]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_368640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 368640 = ⟨1362074261, 2047718881⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_184320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_376833 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 376833 = ⟨698407350, 1437727494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_188416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_385024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 385024 = ⟨914918274, 1369105915⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_192512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_393224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 393224 = ⟨703794704, 201723333⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_196612]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_401408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 401408 = ⟨245650224, 1174726897⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_200704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_409601 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 409601 = ⟨1239725696, 930841682⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_204800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_417792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 417792 = ⟨1755458239, 1807540371⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_208896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_425986 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 425986 = ⟨1652395494, 1533698269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_212993]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_434176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 434176 = ⟨386684296, 1363813538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_217088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_442369 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 442369 = ⟨1257095282, 1272241133⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_221184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_450560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 450560 = ⟨818224288, 1972399941⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_225280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_458756 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 458756 = ⟨618111261, 1018444208⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_229378]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_466944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 466944 = ⟨1055871441, 345775465⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_233472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_475137 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 475137 = ⟨368604533, 819852527⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_237568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_483328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 483328 = ⟨1776630073, 603111274⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_241664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_491522 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 491522 = ⟨1150425697, 614752078⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_245761]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_499712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 499712 = ⟨836848068, 529120781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_249856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_507905 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 507905 = ⟨1270692180, 876052653⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_253952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_516096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 516096 = ⟨1444319707, 1095294811⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_258048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_524320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 524320 = ⟨1205432805, 1585930621⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_262160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_540673 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 540673 = ⟨1455367236, 1400886595⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_270336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_557058 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 557058 = ⟨1061543528, 1780774530⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_278529]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_573441 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 573441 = ⟨1206714176, 1884110491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_286720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_589828 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 589828 = ⟨490610241, 648348660⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_294914]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_606209 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 606209 = ⟨1919830624, 609511007⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_303104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_622594 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 622594 = ⟨1091221647, 1209455664⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_311297]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_638977 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 638977 = ⟨625791716, 231158099⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_319488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_655368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 655368 = ⟨1529481444, 1656574511⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_327684]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_671745 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 671745 = ⟨1781472960, 1655736321⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_335872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_688130 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 688130 = ⟨1154480547, 1571736168⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_344065]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_704513 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 704513 = ⟨1442719341, 1068898366⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_352256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_720900 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 720900 = ⟨1860725748, 2125360214⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_360450]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_737281 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 737281 = ⟨745788814, 487168000⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_368640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_753666 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 753666 = ⟨1818215931, 2145287630⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_376833]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_770049 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 770049 = ⟨1372918299, 1671026959⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_385024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_786448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 786448 = ⟨1103791890, 1881329426⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_393224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_802817 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 802817 = ⟨753308190, 1470108905⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_401408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_819202 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 819202 = ⟨25522602, 1372066603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_409601]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_835585 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 835585 = ⟨597009241, 500073029⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_417792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_851972 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 851972 = ⟨169332264, 1247394275⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_425986]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_868353 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 868353 = ⟨276502439, 722354865⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_434176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_884738 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 884738 = ⟨1865917894, 1695625634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_442369]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_901121 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 901121 = ⟨712352492, 835457699⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_450560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_917512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 917512 = ⟨1835820625, 2046187669⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_458756]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_933889 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 933889 = ⟨464677453, 1727459710⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_466944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_950274 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 950274 = ⟨2092114068, 1654317720⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_475137]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_966657 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 966657 = ⟨11131541, 981833628⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_483328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_983044 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 983044 = ⟨204437272, 1948671090⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_491522]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_999425 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 999425 = ⟨460094964, 1222622832⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_499712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1015810 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1015810 = ⟨794735859, 385280257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_507905]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1032193 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1032193 = ⟨78938012, 2136027882⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_516096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1048640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1048640 = ⟨1853179182, 676208393⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_524320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1081346 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1081346 = ⟨449466483, 2131446523⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_540673]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1114116 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1114116 = ⟨1763634850, 1110279795⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_557058]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1146882 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1146882 = ⟨165045236, 1867883951⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_573441]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1179656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1179656 = ⟨1467687094, 277969363⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_589828]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1212418 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1212418 = ⟨1288761094, 1628742881⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_606209]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1245188 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1245188 = ⟨1586333807, 394875029⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_622594]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1277954 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1277954 = ⟨804447790, 655080013⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_638977]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1310736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1310736 = ⟨135904004, 611278473⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_655368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1343490 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1343490 = ⟨1284462733, 1355237329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_671745]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1376260 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1376260 = ⟨1275957730, 1262368320⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_688130]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1409026 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1409026 = ⟨1135352868, 1827005935⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_704513]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1441800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1441800 = ⟨1337851974, 1786134556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_720900]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1474562 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1474562 = ⟨1582517456, 1371522721⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_737281]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1507332 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1507332 = ⟨1515213747, 861178898⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_753666]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1540098 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1540098 = ⟨1494071522, 1430926357⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_770049]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1572896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1572896 = ⟨1794760137, 1526222685⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_786448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1605634 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1605634 = ⟨35438236, 159672406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_802817]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1638404 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1638404 = ⟨1111509905, 21303407⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_819202]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1671170 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1671170 = ⟨1534194280, 1180635666⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_835585]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1703944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1703944 = ⟨603997638, 1370953657⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_851972]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1736706 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1736706 = ⟨1032935027, 2109944043⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_868353]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1769476 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1769476 = ⟨1981735345, 2144423229⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_884738]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1802242 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1802242 = ⟨586830126, 1038097561⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_901121]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1835024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1835024 = ⟨697253728, 1824058329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_917512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1867778 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1867778 = ⟨107753826, 72406402⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_933889]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1900548 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1900548 = ⟨1496497848, 476844587⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_950274]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1933314 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1933314 = ⟨649721914, 1380678715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_966657]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1966088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1966088 = ⟨1723896923, 689743620⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_983044]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1998850 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1998850 = ⟨57713487, 1479955155⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_999425]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2031620 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2031620 = ⟨1539629883, 1545801366⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1015810]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2064386 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2064386 = ⟨642833185, 770072217⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1032193]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2097280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2097280 = ⟨1814011191, 2023235829⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1048640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2162692 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2162692 = ⟨1623132218, 944533327⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1081346]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2228232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2228232 = ⟨226282239, 759343673⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1114116]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2293764 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2293764 = ⟨1466981224, 1494888231⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1146882]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2359312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2359312 = ⟨1169666200, 2125830572⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1179656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2424836 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2424836 = ⟨235620875, 318327298⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1212418]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2490376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2490376 = ⟨967391750, 563735619⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1245188]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2555908 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2555908 = ⟨1741274234, 936254787⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1277954]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2621472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2621472 = ⟨533997880, 1660267537⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1310736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2686980 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2686980 = ⟨1675898544, 822369931⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1343490]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2752520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2752520 = ⟨42718305, 792075666⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1376260]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2818052 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2818052 = ⟨511570914, 1900181930⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1409026]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2883600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2883600 = ⟨455830278, 786503158⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1441800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2949124 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2949124 = ⟨1457352718, 913600560⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1474562]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3014664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3014664 = ⟨233664139, 381607670⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1507332]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3080196 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3080196 = ⟨1558019117, 481402615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1540098]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3145792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3145792 = ⟨2099039696, 300654289⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1572896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3211268 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3211268 = ⟨1613346545, 1331640920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1605634]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3276808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3276808 = ⟨171011252, 1554917184⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1638404]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3342340 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3342340 = ⟨760899767, 265891512⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1671170]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3407888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3407888 = ⟨440989894, 1341768346⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1703944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3473412 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3473412 = ⟨1848198696, 57506270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1736706]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3538952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3538952 = ⟨183183334, 1801821085⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1769476]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3604484 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3604484 = ⟨1380585938, 793258521⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1802242]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3670048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3670048 = ⟨1423806929, 1405976751⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1835024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3735556 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3735556 = ⟨420631344, 2109610824⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1867778]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3801096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3801096 = ⟨2017235755, 1824179252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1900548]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3866628 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3866628 = ⟨1886899566, 1308134881⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1933314]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3932176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3932176 = ⟨1776995599, 1400683592⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1966088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3997700 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3997700 = ⟨1321908813, 241015876⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1998850]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4063240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4063240 = ⟨1604952852, 567543904⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2031620]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4128772 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4128772 = ⟨257122015, 576253627⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2064386]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4194560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4194560 = ⟨1852294617, 1759311057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2097280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4325384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4325384 = ⟨534687019, 1989415451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2162692]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4456464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4456464 = ⟨1591114189, 439540954⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2228232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4587528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4587528 = ⟨247231043, 1084755678⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2293764]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4718624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4718624 = ⟨305453183, 551711442⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2359312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4849672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4849672 = ⟨1338878803, 1485530408⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2424836]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4980752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4980752 = ⟨1578671896, 922836602⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2490376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5111816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5111816 = ⟨83797719, 589556384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2555908]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5242944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5242944 = ⟨1184513982, 1207420494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2621472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5373960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5373960 = ⟨1072730109, 773159090⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2686980]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5505040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5505040 = ⟨724011080, 1315508163⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2752520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5636104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5636104 = ⟨614249355, 173120158⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2818052]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5767200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5767200 = ⟨1426901000, 863202923⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2883600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5898248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5898248 = ⟨408329432, 330245484⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2949124]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6029328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6029328 = ⟨2033935536, 256945801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3014664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6160392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6160392 = ⟨2056979281, 1351208030⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3080196]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6291584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6291584 = ⟨176300780, 1979519110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3145792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6422536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6422536 = ⟨1213750725, 2142473495⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3211268]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6553616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6553616 = ⟨935351618, 1531443938⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3276808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6684680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6684680 = ⟨1663436953, 856777537⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3342340]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6815776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6815776 = ⟨1024200603, 2128350496⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3407888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6946824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6946824 = ⟨363972680, 1205722297⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3473412]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7077904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7077904 = ⟨2127864263, 2022568055⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3538952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7208968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7208968 = ⟨387531755, 1060868495⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3604484]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7340096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7340096 = ⟨1817802522, 379073844⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3670048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7471112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7471112 = ⟨1700964411, 73215633⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3735556]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7602192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7602192 = ⟨594031529, 146193017⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3801096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7733256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7733256 = ⟨132048332, 1694970900⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3866628]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7864352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7864352 = ⟨1386470409, 1542738150⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3932176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7995400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7995400 = ⟨1261477527, 1214408865⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3997700]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8126480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8126480 = ⟨798118118, 1293677959⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4063240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8257544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8257544 = ⟨389057940, 1706873853⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4128772]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8389120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8389120 = ⟨1367393343, 678723808⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4194560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8650768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8650768 = ⟨2068646133, 571924046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4325384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8912928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8912928 = ⟨1575465179, 92686707⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4456464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9175056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9175056 = ⟨909383662, 841524367⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4587528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9437248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9437248 = ⟨311100267, 2031821793⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4718624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9699344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9699344 = ⟨44977590, 1140827221⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4849672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9961504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9961504 = ⟨957743439, 593260259⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4980752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10223632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10223632 = ⟨1864555321, 853125520⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5111816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10485888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10485888 = ⟨517013818, 1419850896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5242944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10747920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10747920 = ⟨1654285252, 722585302⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5373960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11010080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11010080 = ⟨437411851, 1075909444⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5505040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11272208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11272208 = ⟨1670980762, 961414760⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5636104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11534400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11534400 = ⟨1260320354, 1076210634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5767200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11796496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11796496 = ⟨196171608, 423040992⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5898248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12058656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12058656 = ⟨1192803800, 695452884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6029328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12320784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12320784 = ⟨1528984411, 1578845943⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6160392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12583168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12583168 = ⟨1520486054, 376538128⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6291584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12845072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12845072 = ⟨626573359, 2130979868⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6422536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13107232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13107232 = ⟨1733992080, 473669037⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6553616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13369360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13369360 = ⟨1627756565, 761655914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6684680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13631552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13631552 = ⟨1697779638, 1543719284⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6815776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13893648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13893648 = ⟨1205584328, 1071359737⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6946824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14155808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14155808 = ⟨1929367763, 1294040918⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7077904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14417936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14417936 = ⟨673965627, 2085516600⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7208968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14680192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14680192 = ⟨644402256, 482973198⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7340096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14942224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14942224 = ⟨873395777, 1744801402⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7471112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15204384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15204384 = ⟨118500682, 1823508403⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7602192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15466512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15466512 = ⟨153419697, 1573088590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7733256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15728704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15728704 = ⟨1407219712, 903444022⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7864352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15990800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15990800 = ⟨34837187, 1151891895⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7995400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16252960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16252960 = ⟨1261261466, 1627283491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8126480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16515088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16515088 = ⟨67093943, 1033296229⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8257544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16778240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16778240 = ⟨1319895764, 573785706⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8389120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17301536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17301536 = ⟨284224538, 507731155⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8650768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17825856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17825856 = ⟨278419313, 1013247346⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8912928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18350112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18350112 = ⟨1942050127, 1773587075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9175056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18874496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18874496 = ⟨165330256, 485749655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9437248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19398688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19398688 = ⟨639285849, 851310998⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9699344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19923008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19923008 = ⟨35038887, 1350087003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9961504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20447264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20447264 = ⟨179970252, 1335301638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10223632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20971776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20971776 = ⟨1078042105, 1465180658⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10485888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21495840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21495840 = ⟨357343769, 114629138⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10747920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22020160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22020160 = ⟨1304917056, 1895465269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11010080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22544416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22544416 = ⟨1570672887, 1428866646⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11272208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23068800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23068800 = ⟨140352376, 1839393940⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11534400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23592992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23592992 = ⟨1830600172, 276168930⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11796496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24117312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24117312 = ⟨965491527, 298427003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12058656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24641568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24641568 = ⟨370397000, 1656999582⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12320784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25166336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25166336 = ⟨1134569950, 659032042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12583168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25690144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25690144 = ⟨586689162, 454082287⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12845072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26214464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26214464 = ⟨634671279, 451861035⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13107232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26738720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26738720 = ⟨2104154350, 328081573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13369360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27263104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27263104 = ⟨538956679, 34943492⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13631552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27787296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27787296 = ⟨1852629255, 212945222⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13893648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28311616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28311616 = ⟨67531337, 1678745528⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14155808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28835872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28835872 = ⟨1190600983, 1973482742⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14417936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29360384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29360384 = ⟨1596739640, 1774906706⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14680192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29884448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29884448 = ⟨844254378, 1871234502⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14942224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30408768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30408768 = ⟨2068693189, 841099615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15204384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30933024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30933024 = ⟨933408270, 1129593282⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15466512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31457408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31457408 = ⟨1584220808, 132481892⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15728704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31981600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31981600 = ⟨1379614777, 853699597⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15990800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32505920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32505920 = ⟨434397945, 1742659280⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16252960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33030176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33030176 = ⟨181029464, 827291109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16515088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34603072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34603072 = ⟨427550274, 1282844241⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17301536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35651712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35651712 = ⟨745117209, 830871608⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17825856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36700224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36700224 = ⟨1081356125, 1812317922⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18350112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37748992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37748992 = ⟨839049945, 1304852283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18874496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38797376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38797376 = ⟨841133652, 796098409⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19398688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39846016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39846016 = ⟨1517515855, 1841146188⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19923008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40894528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40894528 = ⟨991136941, 609987810⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20447264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41943552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41943552 = ⟨1952331673, 349489276⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20971776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42991680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42991680 = ⟨101577476, 2073295470⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21495840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44040320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44040320 = ⟨1058700625, 1309416981⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22020160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45088832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45088832 = ⟨2062023372, 1114154156⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22544416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46137600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46137600 = ⟨676134982, 1159052134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23068800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47185984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47185984 = ⟨1527944948, 1482666666⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23592992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48234624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48234624 = ⟨914528315, 1531142268⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24117312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49283136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49283136 = ⟨547925282, 734895592⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24641568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50332672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50332672 = ⟨1747362177, 1031300071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25166336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51380288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51380288 = ⟨1207866435, 646847996⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25690144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52428928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52428928 = ⟨954723554, 1879873041⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26214464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53477440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53477440 = ⟨127601740, 72441917⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26738720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54526208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54526208 = ⟨1662223803, 1087437408⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27263104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55574592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55574592 = ⟨233937701, 1702189968⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27787296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56623232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56623232 = ⟨757268624, 1041499408⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28311616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57671744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57671744 = ⟨872559303, 1597354532⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28835872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58720768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58720768 = ⟨105760085, 714968132⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29360384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59768896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59768896 = ⟨1598800741, 966689363⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29884448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60817536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60817536 = ⟨417557150, 1952365523⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30408768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61866048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61866048 = ⟨947604018, 197758761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30933024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62914816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62914816 = ⟨1717016081, 1923088208⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31457408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63963200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63963200 = ⟨1181557966, 1111086086⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31981600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65011840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65011840 = ⟨839960757, 1588226628⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32505920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66060352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66060352 = ⟨314553120, 1350416367⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33030176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69206144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69206144 = ⟨1999834566, 1649389020⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34603072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71303424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71303424 = ⟨1071151477, 283131836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35651712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73400448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73400448 = ⟨721404215, 1154702720⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36700224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_75497984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 75497984 = ⟨1474574965, 1789713676⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37748992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77594752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77594752 = ⟨1364384333, 638470926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38797376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_79692032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79692032 = ⟨2138630182, 1104939831⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39846016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_81789056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81789056 = ⟨276785961, 1612347382⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40894528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_83887104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83887104 = ⟨1685341984, 359481912⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41943552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_85983360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 85983360 = ⟨180605114, 1827239478⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42991680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88080640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88080640 = ⟨1573951727, 2017707685⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44040320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90177664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90177664 = ⟨1874713124, 1448514039⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45088832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92275200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92275200 = ⟨764986179, 247410521⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46137600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94371968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94371968 = ⟨406754252, 360024438⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47185984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_96469248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96469248 = ⟨1666295440, 793562241⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48234624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98566272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98566272 = ⟨1947753143, 1625539281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49283136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102760576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102760576 = ⟨983556272, 1954420867⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51380288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104857856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104857856 = ⟨682890760, 825711995⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52428928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106954880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106954880 = ⟨438685551, 297285800⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53477440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_109052416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109052416 = ⟨479992033, 604803335⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54526208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_111149184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 111149184 = ⟨2053725645, 201830937⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55574592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_113246464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 113246464 = ⟨781577710, 78493966⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56623232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115343488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115343488 = ⟨77611000, 889186797⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57671744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_117441536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117441536 = ⟨320524274, 1536842560⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58720768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_119537792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119537792 = ⟨512184694, 1040893596⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59768896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121635072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121635072 = ⟨1256467222, 1844288705⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60817536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123732096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123732096 = ⟨888312544, 760001105⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61866048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125829632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125829632 = ⟨1790148725, 941458893⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62914816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_127926400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 127926400 = ⟨1458349611, 1991186977⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63963200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_130023680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 130023680 = ⟨1998642674, 1167227560⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65011840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_132120704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 132120704 = ⟨329882356, 417114612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66060352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_138412288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 138412288 = ⟨21327419, 799792189⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69206144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_142606848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 142606848 = ⟨1238411844, 256888179⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71303424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_146800896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 146800896 = ⟨800038723, 957017165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73400448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_150995968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 150995968 = ⟨1614159808, 1309336248⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75497984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_155189504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 155189504 = ⟨38574631, 1572886920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77594752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_159384064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 159384064 = ⟨1378781449, 2053379599⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79692032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_163578112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 163578112 = ⟨1129532515, 1201407033⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81789056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_171966720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 171966720 = ⟨1558517407, 65878904⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85983360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_176161280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 176161280 = ⟨352207516, 1759203430⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88080640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_180355328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 180355328 = ⟨1496017404, 140901520⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90177664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_184550400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 184550400 = ⟨628786761, 140902127⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92275200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_188743936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 188743936 = ⟨1635189031, 1819911943⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94371968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_192938496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 192938496 = ⟨18818425, 1218871748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96469248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_197132544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 197132544 = ⟨1199747006, 1233988264⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98566272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_205521152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 205521152 = ⟨1968982177, 297155734⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102760576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_209715712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 209715712 = ⟨338548421, 466358981⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104857856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_213909760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 213909760 = ⟨1594110753, 1361977507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106954880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_218104832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 218104832 = ⟨638582271, 300788326⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109052416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_222298368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 222298368 = ⟨1530105704, 1597890507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111149184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_226492928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 226492928 = ⟨1514534856, 1364972769⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_113246464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_230686976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 230686976 = ⟨206412222, 2030867600⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115343488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_239075584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 239075584 = ⟨1733279553, 700320412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119537792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_243270144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 243270144 = ⟨1417911517, 65694956⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121635072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_247464192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 247464192 = ⟨861294099, 1882879129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123732096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_251659264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 251659264 = ⟨1108016105, 252024370⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125829632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_255852800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 255852800 = ⟨1414987792, 1858058249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_127926400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_260047360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 260047360 = ⟨1335212997, 1278610483⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_130023680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_264241408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 264241408 = ⟨1575970455, 82374263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_132120704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_276824576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 276824576 = ⟨579860981, 1582323443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_138412288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_285213696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 285213696 = ⟨614428895, 566940551⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_142606848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_293601792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 293601792 = ⟨417622760, 1862656935⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_146800896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_310379008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 310379008 = ⟨723251, 1215373430⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_155189504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_318768128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 318768128 = ⟨45393311, 1630721361⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_159384064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_327156224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 327156224 = ⟨684503275, 1668785231⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_163578112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_343933440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 343933440 = ⟨197214865, 1363907272⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_171966720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_352322560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 352322560 = ⟨1152154081, 2106306808⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_176161280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_360710656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 360710656 = ⟨2035170391, 906682662⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_180355328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_377487872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 377487872 = ⟨1425293480, 1007880048⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_188743936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_385876992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 385876992 = ⟨362376885, 1168590975⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_192938496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_394265088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 394265088 = ⟨52536017, 44813674⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_197132544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_411042304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 411042304 = ⟨1004263712, 295126399⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_205521152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_419431424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 419431424 = ⟨20753985, 1635511764⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_209715712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_427819520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 427819520 = ⟨1334627474, 1183000629⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_213909760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_444596736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 444596736 = ⟨1233223129, 115692509⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_222298368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_452985856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 452985856 = ⟨1117531616, 1012065003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_226492928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_461373952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 461373952 = ⟨1402915269, 774227847⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_230686976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_478151168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 478151168 = ⟨1959079929, 503318430⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_239075584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_486540288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 486540288 = ⟨1412610045, 1446210525⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_243270144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_494928384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 494928384 = ⟨1716857761, 1854699285⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_247464192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_511705600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 511705600 = ⟨82106478, 1745301350⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_255852800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_520094720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 520094720 = ⟨1225642256, 1294224634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_260047360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_528482816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 528482816 = ⟨1677499339, 674692256⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_264241408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_553649152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 553649152 = ⟨573785706, 827587883⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_276824576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_587203584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 587203584 = ⟨1031300071, 400121470⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_293601792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_620758016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 620758016 = ⟨359481912, 462141663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_310379008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_654312448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 654312448 = ⟨1536842560, 1826959373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_327156224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_687866880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 687866880 = ⟨1309336248, 533323839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_343933440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_721421312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 721421312 = ⟨140902127, 1518696886⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_360710656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_754975744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 754975744 = ⟨300788326, 1508901376⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_377487872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_788530176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 788530176 = ⟨252024370, 1039467542⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_394265088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_822084608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 822084608 = ⟨566940551, 1533054752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_411042304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_855639040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 855639040 = ⟨1630721361, 2102090336⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_427819520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_889193472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 889193472 = ⟨2106306808, 995329566⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_444596736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_922747904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 922747904 = ⟨1168590975, 1785106762⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_461373952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_956302336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 956302336 = ⟨1635511764, 2126729662⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_478151168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_989856768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 989856768 = ⟨1012065003, 1029952031⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_494928384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1023411200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1023411200 = ⟨1446210525, 734873602⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_511705600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1056965632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1056965632 = ⟨1294224634, 921841391⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_528482816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 32) = ⟨1319895764, 573785706⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 32 = 16778240 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_16778240

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1319895764, 573785706⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 32) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 33) = ⟨573785706, 827587883⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 33 = 553649152 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_553649152

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨573785706, 827587883⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 33) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 34) = ⟨614428895, 566940551⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 34 = 285213696 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_285213696

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨614428895, 566940551⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 34) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 35) = ⟨566940551, 1533054752⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 35 = 822084608 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_822084608

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨566940551, 1533054752⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 35) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 36) = ⟨1614159808, 1309336248⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 36 = 150995968 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_150995968

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1614159808, 1309336248⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 36) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 37) = ⟨1309336248, 533323839⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 37 = 687866880 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_687866880

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1309336248, 533323839⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 37) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 38) = ⟨20753985, 1635511764⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 38 = 419431424 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_419431424

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨20753985, 1635511764⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 38) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 39) = ⟨1635511764, 2126729662⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 39 = 956302336 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_956302336

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1635511764, 2126729662⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 39) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 40) = ⟨1685341984, 359481912⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 40 = 83887104 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_83887104

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1685341984, 359481912⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 40) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 41) = ⟨359481912, 462141663⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 41 = 620758016 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_620758016

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨359481912, 462141663⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 41) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 42) = ⟨1152154081, 2106306808⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 42 = 352322560 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_352322560

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1152154081, 2106306808⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 42) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 43) = ⟨2106306808, 995329566⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 43 = 889193472 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_889193472

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2106306808, 995329566⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 43) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 44) = ⟨638582271, 300788326⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 44 = 218104832 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_218104832

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨638582271, 300788326⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 44) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 45) = ⟨300788326, 1508901376⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 45 = 754975744 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_754975744

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨300788326, 1508901376⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 45) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 46) = ⟨1412610045, 1446210525⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 46 = 486540288 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_486540288

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1412610045, 1446210525⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 46) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 47) = ⟨1446210525, 734873602⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 47 = 1023411200 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1023411200

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1446210525, 734873602⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 47) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 48) = ⟨1747362177, 1031300071⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 48 = 50332672 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_50332672

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1747362177, 1031300071⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 48) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 49) = ⟨1031300071, 400121470⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 49 = 587203584 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_587203584

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1031300071, 400121470⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 49) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 50) = ⟨45393311, 1630721361⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 50 = 318768128 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_318768128

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨45393311, 1630721361⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 50) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 51) = ⟨1630721361, 2102090336⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 51 = 855639040 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_855639040

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1630721361, 2102090336⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 51) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 52) = ⟨628786761, 140902127⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 52 = 184550400 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_184550400

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨628786761, 140902127⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 52) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 53) = ⟨140902127, 1518696886⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 53 = 721421312 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_721421312

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨140902127, 1518696886⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 53) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 54) = ⟨1117531616, 1012065003⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 54 = 452985856 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_452985856

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1117531616, 1012065003⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 54) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 55) = ⟨1012065003, 1029952031⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 55 = 989856768 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_989856768

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1012065003, 1029952031⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 55) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 56) = ⟨320524274, 1536842560⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 56 = 117441536 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_117441536

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨320524274, 1536842560⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 56) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 57) = ⟨1536842560, 1826959373⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 57 = 654312448 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_654312448

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1536842560, 1826959373⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 57) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 58) = ⟨362376885, 1168590975⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 58 = 385876992 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_385876992

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨362376885, 1168590975⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 58) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 59) = ⟨1168590975, 1785106762⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 59 = 922747904 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_922747904

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1168590975, 1785106762⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 59) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 60) = ⟨1108016105, 252024370⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 60 = 251659264 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_251659264

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1108016105, 252024370⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 60) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 61) = ⟨252024370, 1039467542⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 61 = 788530176 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_788530176

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨252024370, 1039467542⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 61) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 62) = ⟨1225642256, 1294224634⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 62 = 520094720 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_520094720

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1225642256, 1294224634⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 62) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 63) = ⟨1294224634, 921841391⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 63 = 1056965632 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1056965632

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1294224634, 921841391⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 63) := by
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

end R17TableAChunk01Certificate
