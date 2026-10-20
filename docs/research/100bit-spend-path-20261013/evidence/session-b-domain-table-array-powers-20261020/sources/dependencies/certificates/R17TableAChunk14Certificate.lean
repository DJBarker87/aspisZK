import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk14Certificate
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

theorem power_65 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65 = ⟨1106294891, 184370010⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_67 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67 = ⟨1982486292, 1611456260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69 = ⟨878709433, 901181160⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71 = ⟨1729511182, 267661745⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73 = ⟨1859610645, 698599623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36]
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

theorem power_81 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81 = ⟨1283630603, 1419035398⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_83 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83 = ⟨1069733101, 25059729⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_85 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 85 = ⟨807730929, 1079284455⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87 = ⟨1648565317, 52537112⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89 = ⟨797347039, 1803718760⟩ := by
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

theorem power_93 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93 = ⟨1406255700, 949804171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_97 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 97 = ⟨1433319239, 2069664066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_99 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 99 = ⟨1303248187, 75374765⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_101 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101 = ⟨1779769850, 1133066291⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_103 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103 = ⟨2138693243, 755167780⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105 = ⟨244648141, 849348041⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_107 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 107 = ⟨1286380731, 398286559⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53]
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

theorem power_112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112 = ⟨2110227055, 661472412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_113 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 113 = ⟨1539908113, 1295392627⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115 = ⟨1772811593, 1752614228⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_117 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117 = ⟨1804617719, 1766370095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_119 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119 = ⟨2017000003, 1501730632⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121 = ⟨663578559, 2077989577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60]
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

theorem power_131 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131 = ⟨95247863, 1577442507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_135 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 135 = ⟨1083123019, 1628198916⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_139 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 139 = ⟨1724704064, 760534735⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_142 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 142 = ⟨2045471800, 21567742⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_147 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 147 = ⟨1871749785, 872210914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_151 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 151 = ⟨1692705482, 1818541172⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_155 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 155 = ⟨95599379, 1884941993⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_156 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 156 = ⟨58128200, 444904138⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_163 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 163 = ⟨1027654423, 1354925944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_167 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 167 = ⟨2122757670, 2074642722⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_171 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 171 = ⟨617956980, 1693803782⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_174 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 174 = ⟨1566056996, 1745888105⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_179 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 179 = ⟨64917534, 1646995590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89]
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

theorem power_187 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 187 = ⟨799610937, 665210564⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_195 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 195 = ⟨1952223760, 1817980554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_97]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_199 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 199 = ⟨328392223, 1882866834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_203 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 203 = ⟨1626325386, 533448899⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_206 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 206 = ⟨891793723, 1417325858⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_211 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 211 = ⟨2040897111, 1468235903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_215 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 215 = ⟨1298411934, 695435615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_107]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_219 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 219 = ⟨742915033, 302287293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109]
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

theorem power_227 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 227 = ⟨881338165, 1738354347⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_113]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_231 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 231 = ⟨235212131, 119569981⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_235 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 235 = ⟨1800142309, 2130869144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_238 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 238 = ⟨1707325511, 1098406816⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_243 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 243 = ⟨1155190479, 56664675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_247 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 247 = ⟨1816092284, 1450828631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_251 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 251 = ⟨1126878156, 83731982⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_263 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 263 = ⟨264164055, 532059872⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_270 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 270 = ⟨529601202, 621421182⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_135]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_279 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 279 = ⟨269846636, 1112027874⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_139]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_284 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 284 = ⟨23079860, 1037577460⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_142]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_295 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 295 = ⟨1957423892, 1814157310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_147]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_302 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 302 = ⟨2109094984, 117233691⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_151]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_311 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 311 = ⟨22732032, 144031577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_155]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 312 = ⟨715656401, 189653281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_156]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_327 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 327 = ⟨1737134773, 1303677580⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_163]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_334 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 334 = ⟨753378315, 1427449060⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_167]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_343 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 343 = ⟨1798881283, 934839227⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_171]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_348 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 348 = ⟨1388299958, 1206426289⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_174]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_359 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 359 = ⟨1272967278, 2025901232⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_179]
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

theorem power_375 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 375 = ⟨1877760225, 331420888⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_187]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_391 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 391 = ⟨37190064, 608223695⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_195]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_398 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 398 = ⟨1915229291, 1105504804⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_199]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_407 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 407 = ⟨715726346, 1941423518⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_203]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_412 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 412 = ⟨2105482584, 779799999⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_206]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_423 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 423 = ⟨2052487374, 255150963⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_211]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_430 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 430 = ⟨263286599, 1282534279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_215]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_439 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 439 = ⟨1554663367, 1278324319⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_219]
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

theorem power_455 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 455 = ⟨1435998008, 149405312⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_227]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_462 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 462 = ⟨942972626, 1810202834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_231]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_471 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 471 = ⟨474268017, 931879591⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_235]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_476 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 476 = ⟨795892619, 307427987⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_238]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_487 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 487 = ⟨1295993054, 428314053⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_243]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_494 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 494 = ⟨1055176129, 673017746⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_247]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_503 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 503 = ⟨1201144034, 801609829⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_251]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_526 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 526 = ⟨829590764, 277235238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_263]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_540 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 540 = ⟨630512252, 401771957⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_270]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_558 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 558 = ⟨1491117715, 1287088226⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_279]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 568 = ⟨1827897087, 929922642⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_284]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_590 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 590 = ⟨1574728984, 172614345⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_295]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_604 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 604 = ⟨538020577, 631501536⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_302]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_622 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 622 = ⟨1167677415, 1226977591⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_311]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 624 = ⟨1784074070, 421362258⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_654 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 654 = ⟨1911626802, 1408919644⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_327]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_668 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 668 = ⟨426899686, 373278555⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_334]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_686 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 686 = ⟨1514861678, 1695906622⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_343]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 696 = ⟨1453440674, 589119313⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_348]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_718 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 718 = ⟨1155058076, 256007307⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_359]
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

theorem power_750 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 750 = ⟨2065836190, 1485240130⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_375]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_782 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 782 = ⟨117660080, 343121219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_391]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_796 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 796 = ⟨700492617, 8678681⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_398]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_814 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 814 = ⟨98854679, 745200030⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_407]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 824 = ⟨393192345, 1269883945⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_412]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_846 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 846 = ⟨1621994735, 1524064569⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_423]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_860 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 860 = ⟨1223844726, 1188846095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_430]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_878 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 878 = ⟨1728269515, 1349774790⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_439]
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

theorem power_910 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 910 = ⟨1295927611, 252131538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_455]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_924 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 924 = ⟨1091307962, 1671174009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_462]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_942 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 942 = ⟨686004961, 1895201033⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_471]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 952 = ⟨736233126, 745912594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_476]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_974 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 974 = ⟨1497351921, 1855915709⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_487]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_988 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 988 = ⟨930302072, 933399811⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_494]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1006 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1006 = ⟨551041537, 265026071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_503]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1052 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1052 = ⟨1975134191, 1726433108⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_526]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1080 = ⟨2042646259, 94992365⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_540]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1116 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1116 = ⟨1991430005, 1812623788⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_558]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1136 = ⟨934113032, 310511167⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1180 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1180 = ⟨1464176691, 1505037834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_590]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1208 = ⟨176440113, 1084668010⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_604]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1244 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1244 = ⟨944355796, 40782466⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_622]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1248 = ⟨202925653, 1282518697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1308 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1308 = ⟨1163455345, 1600087075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_654]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1336 = ⟨1009955505, 1510543494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_668]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1372 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1372 = ⟨559343046, 936948094⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_686]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1392 = ⟨1354106400, 443181508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1436 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1436 = ⟨907819230, 1630355909⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_718]
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

theorem power_1500 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1500 = ⟨901439843, 934836366⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_750]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1564 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1564 = ⟨870084042, 1579190631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_782]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1592 = ⟨527586588, 1562116815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_796]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1628 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1628 = ⟨1635903323, 1205279639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_814]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1648 = ⟨319382324, 289573192⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1692 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1692 = ⟨1908075611, 957330925⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_846]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1720 = ⟨1990060689, 1173021817⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_860]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1756 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1756 = ⟨560263499, 1428906151⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_878]
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

theorem power_1820 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1820 = ⟨1950843909, 2006402393⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_910]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1848 = ⟨2109320268, 1124983315⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_924]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1884 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1884 = ⟨1267900042, 1493261579⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_942]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1904 = ⟨547307125, 463271940⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1948 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1948 = ⟨719650462, 455110049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_974]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1976 = ⟨816997558, 1117506323⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_988]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2012 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2012 = ⟨1854143625, 1540733942⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1006]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2104 = ⟨1604067772, 1189930395⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1052]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2160 = ⟨1565483443, 2098430477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2232 = ⟨1640638342, 284240914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1116]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2272 = ⟨308268370, 2093673186⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2360 = ⟨1685078008, 1168537700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1180]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2416 = ⟨1645200661, 71941409⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2488 = ⟨890865984, 1319278941⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1244]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2496 = ⟨603512862, 13573590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2616 = ⟨194348792, 1903559392⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1308]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2672 = ⟨1012691958, 881525569⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2744 = ⟨132496696, 1786612251⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1372]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2784 = ⟨1360272642, 462407257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2872 = ⟨2015587695, 679824208⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1436]
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

theorem power_3000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3000 = ⟨1035075470, 95834627⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1500]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3128 = ⟨1720814836, 1068018523⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1564]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3184 = ⟨1911211217, 1209662043⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3256 = ⟨1982169513, 1884943985⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1628]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3296 = ⟨903616870, 1432862237⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3384 = ⟨318899525, 73577497⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1692]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3440 = ⟨1298571999, 1740873419⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3512 = ⟨158945276, 1347273362⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1756]
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

theorem power_3640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3640 = ⟨1626988206, 605179311⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1820]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3696 = ⟨1519898835, 1228368252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3768 = ⟨6961216, 536306813⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1884]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3808 = ⟨1506184608, 1755829396⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3896 = ⟨1511756944, 42542624⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1948]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3952 = ⟨242936601, 625351024⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4024 = ⟨293521131, 2032679990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2012]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4208 = ⟨1643709738, 134208845⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4320 = ⟨126966968, 506934318⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4464 = ⟨2022668959, 36874573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4544 = ⟨609701741, 767315046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4720 = ⟨798461255, 1184415437⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4832 = ⟨513734373, 631097729⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4976 = ⟨1547269505, 282738600⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4992 = ⟨2028012531, 2010507233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5232 = ⟨1774838845, 217149572⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5344 = ⟨1939587010, 1616699649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5488 = ⟨1158738579, 273303797⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5568 = ⟨99211207, 1946280920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5744 = ⟨935877183, 162122437⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2872]
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

theorem power_6000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6000 = ⟨1449763771, 1766629000⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6256 = ⟨2020134253, 1544406249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6368 = ⟨428722550, 108559190⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6512 = ⟨1797646140, 959904052⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6592 = ⟨2029889606, 1568983310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6768 = ⟨738507874, 1072660579⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6880 = ⟨205625603, 17388685⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7024 = ⟨1540490384, 1427395116⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3512]
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

theorem power_7280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7280 = ⟨1934485533, 1555261218⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7392 = ⟨1052737347, 1152187489⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7536 = ⟨1119408201, 1868692566⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7616 = ⟨1101130210, 28496752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7792 = ⟨1477132215, 2092030299⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7904 = ⟨1388086223, 26444797⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8048 = ⟨1150356543, 1061733098⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8416 = ⟨1436022363, 77761227⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8640 = ⟨1961795311, 1082834093⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8928 = ⟨1943481087, 1551211646⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9088 = ⟨236427592, 1624003215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9440 = ⟨920031681, 2067595277⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9664 = ⟨1211655166, 348770789⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9952 = ⟨128433003, 725390371⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9984 = ⟨1723471681, 1868423509⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10464 = ⟨694836955, 1210560494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10688 = ⟨1911771696, 801892733⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10976 = ⟨922554459, 1769170006⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11136 = ⟨147298690, 1099763101⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11488 = ⟨421496146, 643857265⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5744]
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

theorem power_12000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12000 = ⟨753396631, 1636667086⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12512 = ⟨1566125769, 194471801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12736 = ⟨927007817, 1410344259⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13024 = ⟨1405976515, 1750233987⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13184 = ⟨917179047, 586675057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13536 = ⟨1504095847, 1862342457⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13760 = ⟨810420398, 1427461404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14048 = ⟨1013288999, 1806558997⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14080 = ⟨907734057, 1982459870⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14337 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14337 = ⟨2087217776, 405863725⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14560 = ⟨1401520016, 1762276114⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14784 = ⟨1879071391, 1829202452⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15072 = ⟨844934376, 1202477432⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15232 = ⟨1395708858, 1497177230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15584 = ⟨743054035, 949747629⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15808 = ⟨1522548683, 2001077972⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16096 = ⟨2036167106, 1492556602⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16832 = ⟨1733498853, 1039774206⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17280 = ⟨1405370388, 1401549109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17856 = ⟨79784428, 10832239⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18176 = ⟨277390402, 1017102786⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18880 = ⟨172837975, 1734177351⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19328 = ⟨1574695602, 343473568⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19904 = ⟨1384736264, 1508173861⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19968 = ⟨1443152952, 1248797592⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20928 = ⟨1204820228, 887300757⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21376 = ⟨1307076942, 7561917⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21952 = ⟨554824944, 1495951592⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22272 = ⟨1233494247, 815501048⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22976 = ⟨812731445, 1551963465⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11488]
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

theorem power_24000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24000 = ⟨1982026364, 1164148539⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25024 = ⟨1019568096, 167387491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25472 = ⟨1174190859, 1895341634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26048 = ⟨232633419, 916445628⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26368 = ⟨231300344, 22616870⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27072 = ⟨39690763, 702335356⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27520 = ⟨958142641, 463023983⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28096 = ⟨1759697750, 119796228⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28160 = ⟨1780266745, 1890401423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28674 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28674 = ⟨1079453901, 941436350⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14337]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29120 = ⟨1013591108, 679753134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29568 = ⟨1143577263, 1687775453⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30144 = ⟨1588754652, 1732368585⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30464 = ⟨1306202290, 656337007⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31168 = ⟨943541889, 1883727630⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31616 = ⟨2038041307, 395046603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32192 = ⟨1629981853, 1336187357⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33664 = ⟨876725885, 1903584727⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34560 = ⟨989291292, 715603760⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35712 = ⟨61954272, 2019998401⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36352 = ⟨1666103267, 543807372⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37760 = ⟨534515800, 414664150⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38656 = ⟨1994929345, 92888755⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39808 = ⟨1692794093, 651445521⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39936 = ⟨602433585, 1609250172⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41856 = ⟨309849155, 391258082⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42752 = ⟨1211674855, 376154875⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43904 = ⟨898321312, 1952568731⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44544 = ⟨2059734770, 1626927132⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45952 = ⟨530432210, 1653389888⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46848 = ⟨1260104520, 1620860171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47105 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47105 = ⟨147039068, 346401738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48000 = ⟨1258925000, 605866901⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50048 = ⟨520387702, 1851337581⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50944 = ⟨892010052, 235679077⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52096 = ⟨1341140274, 1581753919⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52736 = ⟨559851472, 639516914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54144 = ⟨490093582, 1570661830⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55040 = ⟨690580754, 1235284839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56192 = ⟨1802301119, 1727867741⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56320 = ⟨711796573, 1765055593⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57348 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57348 = ⟨1146892446, 1284782970⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28674]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58240 = ⟨1492559681, 587693506⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59136 = ⟨195201793, 97887997⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60288 = ⟨1109143255, 1622520321⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60928 = ⟨704349578, 1737110009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62336 = ⟨344276509, 1243114512⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63232 = ⟨620105848, 1681908103⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64384 = ⟨1369451326, 208347535⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_67328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67328 = ⟨90855478, 1593497304⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69120 = ⟨1663137283, 90268489⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71424 = ⟨158077892, 536868304⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72704 = ⟨1659670602, 561643989⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_75520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 75520 = ⟨1618108676, 1322812739⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77312 = ⟨105480201, 1515380487⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_79616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79616 = ⟨1658640304, 1654820447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_79873 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79873 = ⟨1654420923, 623226344⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_83712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83712 = ⟨1577027756, 312224782⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_85504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 85504 = ⟨1880924448, 411348355⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87808 = ⟨419048557, 1394878118⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89088 = ⟨1042833731, 101065615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_91904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 91904 = ⟨1832759338, 1768990041⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_93696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93696 = ⟨1605856742, 1072957887⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94210 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94210 = ⟨234868991, 677808164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47105]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_96000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96000 = ⟨1185170578, 768105053⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_100096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100096 = ⟨2003658153, 321424816⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_101888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101888 = ⟨1373722145, 1666977548⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104192 = ⟨659402862, 307320598⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105472 = ⟨652753676, 326975263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108288 = ⟨760378857, 1934298436⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_110080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110080 = ⟨1592908054, 239121665⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_112384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112384 = ⟨670063802, 1807626416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_112641 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112641 = ⟨1444911702, 137990141⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_114696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114696 = ⟨513519395, 2126706955⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57348]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_116480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116480 = ⟨403554188, 1365919173⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_118272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118272 = ⟨530163866, 642094632⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120576 = ⟨192814630, 356994949⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121856 = ⟨1209236572, 1025248382⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124672 = ⟨1224506057, 2118262798⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126464 = ⟨1689711892, 426618051⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_128768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128768 = ⟨162972757, 29423093⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_134656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 134656 = ⟨246392132, 1752206917⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_138240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 138240 = ⟨65347242, 2130122093⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_142848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 142848 = ⟨1865447472, 178474722⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_145409 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 145409 = ⟨1331294845, 1059584374⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_151040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 151040 = ⟨704642966, 1916707119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_154624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 154624 = ⟨1660165387, 1203252895⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_159232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 159232 = ⟨1898545304, 843880917⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_159746 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 159746 = ⟨1409913917, 33465193⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79873]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_167424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 167424 = ⟨424478874, 2078494929⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_171008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 171008 = ⟨221694143, 1124421163⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_175616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 175616 = ⟨49463310, 1992066759⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_178177 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 178177 = ⟨1362103894, 778681703⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_183808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 183808 = ⟨485615949, 1186208873⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_187392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 187392 = ⟨321515844, 1267053385⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_188420 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 188420 = ⟨1548920688, 34342868⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94210]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_192000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 192000 = ⟨1490338342, 2117672798⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_200192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 200192 = ⟨258809902, 922229075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_203776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 203776 = ⟨851041255, 34490752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_208384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 208384 = ⟨1470753755, 941679701⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_210945 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 210945 = ⟨1839032936, 1318020745⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_216576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 216576 = ⟨1933442095, 838049710⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_220160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 220160 = ⟨1138662242, 1124185095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_224768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 224768 = ⟨1838736897, 1889127100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_225282 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 225282 = ⟨2141464617, 775981871⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112641]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_229392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 229392 = ⟨252259448, 499049173⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_232960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 232960 = ⟨270449596, 1156816099⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_236544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 236544 = ⟨366429576, 528662537⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_241152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 241152 = ⟨1811557930, 1082980241⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_243713 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 243713 = ⟨1360969224, 742938978⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_249344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 249344 = ⟨1618238445, 1441802405⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_252928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 252928 = ⟨614226948, 186141612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_257536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 257536 = ⟨1951791511, 358785381⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_269312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 269312 = ⟨514862714, 964544317⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_134656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_276481 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 276481 = ⟨376547610, 1836194247⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_138240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_285696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 285696 = ⟨369514396, 980205573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_142848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_290818 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 290818 = ⟨798469920, 1460064267⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_145409]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_302080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 302080 = ⟨194008892, 454794782⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_151040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_309249 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 309249 = ⟨734903295, 1437666958⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_154624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_318464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 318464 = ⟨178740611, 2113243823⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_159232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_319492 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 319492 = ⟨43668385, 1212926705⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_159746]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_334848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 334848 = ⟨199001272, 1665021225⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_167424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_342017 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 342017 = ⟨355320748, 2112399698⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_171008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_351232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 351232 = ⟨1161610822, 947748647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_175616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_356354 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 356354 = ⟨18403879, 792933022⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_178177]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_367616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 367616 = ⟨1816510680, 2042381711⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_183808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_374785 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 374785 = ⟨278898662, 1091504815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_187392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_376840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 376840 = ⟨1739894304, 1669423493⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_188420]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_384000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 384000 = ⟨2141656184, 1331818282⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_192000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_400384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 400384 = ⟨572977582, 527153650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_200192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_407553 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 407553 = ⟨40023729, 1747003265⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_203776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_416768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 416768 = ⟨754407186, 1989571461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_208384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_421890 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 421890 = ⟨995248673, 168048727⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_210945]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_433152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 433152 = ⟨287842196, 1085363673⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_216576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_440321 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 440321 = ⟨640714442, 1027148468⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_220160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_449536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 449536 = ⟨1331287229, 1368413357⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_224768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_450564 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 450564 = ⟨1346032019, 1319238570⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_225282]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_458784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 458784 = ⟨1943748263, 1894047836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_229392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_465920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 465920 = ⟨394776767, 1670648596⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_232960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_473089 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 473089 = ⟨1353335825, 151815084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_236544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_482304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 482304 = ⟨1390582301, 22370994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_241152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_487426 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 487426 = ⟨884056136, 1481368742⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_243713]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_498688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 498688 = ⟨1894947366, 1922894643⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_249344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_505857 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 505857 = ⟨536451850, 1861214998⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_252928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_515072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 515072 = ⟨1722960484, 1950506513⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_257536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_538625 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 538625 = ⟨585750246, 604947761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_269312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_552962 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 552962 = ⟨1764596579, 2101711339⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_276481]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_571393 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 571393 = ⟨804317074, 1563759547⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_285696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_581636 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 581636 = ⟨1115535542, 1238650813⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_290818]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_604161 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 604161 = ⟨1148225851, 618560277⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_302080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_618498 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 618498 = ⟨853809658, 537976709⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_309249]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_636929 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 636929 = ⟨375531633, 2097360256⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_318464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_638984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 638984 = ⟨2049355741, 97664082⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_319492]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_669697 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 669697 = ⟨1616953613, 2104569820⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_334848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_684034 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 684034 = ⟨923869249, 1192546889⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_342017]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_702465 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 702465 = ⟨1213679792, 467834869⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_351232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_712708 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 712708 = ⟨1135399954, 1609827666⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_356354]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_735233 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 735233 = ⟨1185172592, 423517916⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_367616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_749570 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 749570 = ⟨2146772865, 1027576619⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_374785]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_753680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 753680 = ⟨1323996812, 187584719⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_376840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_768001 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 768001 = ⟨946223378, 2024109503⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_384000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_800769 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 800769 = ⟨1284605699, 2018198022⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_400384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_815106 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 815106 = ⟨1272909933, 1755951520⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_407553]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_833537 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 833537 = ⟨922205880, 1298494696⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_416768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_843780 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 843780 = ⟨1211257596, 1085118304⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_421890]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_866305 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 866305 = ⟨101672005, 568698447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_433152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_880642 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 880642 = ⟨741995426, 1833016867⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_440321]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_899073 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 899073 = ⟨1189076773, 1354447904⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_449536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_901128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 901128 = ⟨1760425679, 1988974618⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_450564]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_917568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 917568 = ⟨1742305819, 2031044834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_458784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_931841 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 931841 = ⟨1362793435, 645303449⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_465920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_946178 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 946178 = ⟨386236774, 1165268044⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_473089]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_964609 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 964609 = ⟨847915220, 146555979⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_482304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_974852 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 974852 = ⟨993442288, 1858000428⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_487426]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_997377 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 997377 = ⟨888713175, 386140044⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_498688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1011714 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1011714 = ⟨1454101620, 1945320900⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_505857]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1030145 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1030145 = ⟨2097723592, 1664212384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_515072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1077250 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1077250 = ⟨154040319, 118871975⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_538625]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1105924 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1105924 = ⟨387438319, 50255418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_552962]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1142786 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1142786 = ⟨1650130289, 144166420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_571393]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1163272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1163272 = ⟨1125680822, 1271335607⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_581636]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1208322 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1208322 = ⟨865095856, 538340570⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_604161]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1236996 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1236996 = ⟨140322263, 520356228⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_618498]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1273858 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1273858 = ⟨1503860250, 1556020864⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_636929]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1277968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1277968 = ⟨234577776, 384338275⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_638984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1339394 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1339394 = ⟨1204554430, 160432206⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_669697]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1368068 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1368068 = ⟨616961286, 1442837283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_684034]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1404930 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1404930 = ⟨1246481557, 85308294⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_702465]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1425416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1425416 = ⟨1867206979, 516367068⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_712708]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1470466 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1470466 = ⟨1520332540, 346203706⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_735233]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1499140 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1499140 = ⟨1104788957, 1840001165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_749570]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1507360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1507360 = ⟨574612467, 1838179464⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_753680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1536002 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1536002 = ⟨2144702892, 1949898540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_768001]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1601538 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1601538 = ⟨1557086113, 471647954⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_800769]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1630212 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1630212 = ⟨1406760135, 126412940⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_815106]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1667074 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1667074 = ⟨427891036, 361341527⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_833537]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1687560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1687560 = ⟨1545482856, 1966189255⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_843780]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1732610 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1732610 = ⟨1196088241, 1680936219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_866305]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1761284 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1761284 = ⟨1251068031, 408461663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_880642]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1798146 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1798146 = ⟨1349238252, 570839268⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_899073]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1802256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1802256 = ⟨1585040814, 1617489360⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_901128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1835136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1835136 = ⟨344613306, 1246019524⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_917568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1863682 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1863682 = ⟨1012594321, 745636355⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_931841]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1892356 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1892356 = ⟨1326440129, 1649320804⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_946178]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1929218 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1929218 = ⟨1578035498, 1089109272⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_964609]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1949704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1949704 = ⟨1734514589, 6539957⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_974852]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1994754 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1994754 = ⟨780611891, 1029884451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_997377]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2023428 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2023428 = ⟨1542472045, 1134216049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1011714]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2060290 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2060290 = ⟨939936638, 139146111⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1030145]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2154500 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2154500 = ⟨219632510, 722016257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1077250]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2211848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2211848 = ⟨320999838, 293448429⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1105924]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2285572 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2285572 = ⟨2078294344, 1721508023⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1142786]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2326544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2326544 = ⟨1616737850, 972831120⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1163272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2416644 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2416644 = ⟨677918723, 234366311⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1208322]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2473992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2473992 = ⟨1756595752, 522213393⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1236996]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2547716 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2547716 = ⟨1939090004, 1131389538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1273858]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2555936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2555936 = ⟨1433836565, 479389356⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1277968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2678788 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2678788 = ⟨1460800609, 1020315834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1339394]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2736136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2736136 = ⟨52770048, 695289984⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1368068]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2809860 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2809860 = ⟨601309264, 801875774⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1404930]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2850832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2850832 = ⟨1671727509, 179900431⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1425416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2940932 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2940932 = ⟨1051340921, 2078337348⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1470466]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2998280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2998280 = ⟨313872392, 1960708081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1499140]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3014720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3014720 = ⟨595186507, 1744445431⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1507360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3072004 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3072004 = ⟨1166998002, 2018778023⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1536002]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3203076 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3203076 = ⟨1660140688, 644732664⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1601538]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3260424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3260424 = ⟨1595985698, 1489998129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1630212]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3334148 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3334148 = ⟨480252505, 2128929253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1667074]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3375120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3375120 = ⟨959476650, 1449340612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1687560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3465220 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3465220 = ⟨690163649, 1970793604⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1732610]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3522568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3522568 = ⟨682346938, 2047900650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1761284]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3596292 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3596292 = ⟨90878799, 1483667716⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1798146]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3604512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3604512 = ⟨1122957447, 947126338⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1802256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3670272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3670272 = ⟨709140113, 2086617698⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1835136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3727364 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3727364 = ⟨1070140378, 2054725664⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1863682]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3784712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3784712 = ⟨1452133597, 1964850959⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1892356]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3858436 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3858436 = ⟨1680262700, 1387152231⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1929218]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3899408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3899408 = ⟨788470901, 213736440⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1949704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3989508 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3989508 = ⟨609260702, 944282830⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1994754]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4046856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4046856 = ⟨2051264714, 1409787800⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2023428]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4120580 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4120580 = ⟨828451010, 996784360⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2060290]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4309000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4309000 = ⟨1382770290, 897568581⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2154500]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4423696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4423696 = ⟨1276446623, 1644238045⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2211848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4571144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4571144 = ⟨1829786934, 1632300781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2285572]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4653088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4653088 = ⟨1251210610, 1967774009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2326544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4833288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4833288 = ⟨384143307, 11519809⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2416644]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4947984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4947984 = ⟨1875195925, 1090465825⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2473992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5095432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5095432 = ⟨821634626, 698576602⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2547716]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5111872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5111872 = ⟨1529552346, 1039370013⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2555936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5357576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5357576 = ⟨1324322880, 569279565⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2678788]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5472272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5472272 = ⟨974754456, 1594779445⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2736136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5619720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5619720 = ⟨19035211, 735028835⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2809860]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5701664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5701664 = ⟨953438745, 1283888531⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2850832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5881864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5881864 = ⟨1226749149, 699486081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2940932]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5996560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5996560 = ⟨1310850860, 1405790046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2998280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6029440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6029440 = ⟨1849661168, 945855072⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3014720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6144008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6144008 = ⟨748346338, 1390060568⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3072004]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6406152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6406152 = ⟨562410423, 1166582385⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3203076]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6520848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6520848 = ⟨1704294598, 1915843008⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3260424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6668296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6668296 = ⟨1575937610, 434817188⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3334148]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6750240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6750240 = ⟨1126091900, 1987047545⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3375120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6930440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6930440 = ⟨1575837285, 1814250764⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3465220]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7045136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7045136 = ⟨347848588, 985101892⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3522568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7192584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7192584 = ⟨578585257, 730162044⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3596292]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7209024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7209024 = ⟨378800964, 144347258⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3604512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7340544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7340544 = ⟨40433138, 940443632⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3670272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7454728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7454728 = ⟨290665003, 528674213⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3727364]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7569424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7569424 = ⟨198458961, 2045218803⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3784712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7716872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7716872 = ⟨967406055, 2015420469⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3858436]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7798816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7798816 = ⟨587353280, 1923035886⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3899408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7979016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7979016 = ⟨1722363821, 2141156338⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3989508]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8093712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8093712 = ⟨1637651110, 1182997888⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4046856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8241160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8241160 = ⟨18595824, 866902852⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4120580]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8618000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8618000 = ⟨314179655, 999497302⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4309000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8847392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8847392 = ⟨722608772, 1698659667⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4423696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9142288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9142288 = ⟨940930355, 598909230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4571144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9306176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9306176 = ⟨1063668526, 1135549277⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4653088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9666576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9666576 = ⟨1947590710, 501842452⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4833288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9895968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9895968 = ⟨1751702968, 1899575128⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4947984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10190864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10190864 = ⟨162583896, 18779211⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5095432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10223744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10223744 = ⟨256701752, 157069318⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5111872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10715152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10715152 = ⟨854298710, 1773697774⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5357576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10944544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10944544 = ⟨1610733674, 1366821843⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5472272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11239440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11239440 = ⟨1569014303, 1401424519⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5619720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11403328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11403328 = ⟨971922669, 2038891920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5701664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11763728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11763728 = ⟨783362277, 936307801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5881864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11993120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11993120 = ⟨247746346, 1537100510⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5996560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12058880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12058880 = ⟨69670920, 1181221219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6029440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12288016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12288016 = ⟨278875155, 1164547572⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6144008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12812304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12812304 = ⟨1647170118, 207092355⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6406152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13041696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13041696 = ⟨942249104, 501264159⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6520848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13336592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13336592 = ⟨325051347, 993827002⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6668296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13500480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13500480 = ⟨925909781, 1380187098⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6750240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13860880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13860880 = ⟨561640039, 1769315816⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6930440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14090272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14090272 = ⟨309061532, 1971349278⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7045136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14385168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14385168 = ⟨124085296, 1455083996⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7192584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14418048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14418048 = ⟨1983181393, 1654670699⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7209024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14681088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14681088 = ⟨300510473, 181714998⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7340544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14909456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14909456 = ⟨337528126, 1180043021⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7454728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15138848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15138848 = ⟨2027315337, 826465859⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7569424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15433744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15433744 = ⟨457904227, 1568194033⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7716872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15597632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15597632 = ⟨657171462, 326427465⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7798816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15958032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15958032 = ⟨1396899081, 1146163711⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7979016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16187424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16187424 = ⟨1233363675, 1597733856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8093712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16482320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16482320 = ⟨1494543366, 1487318663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8241160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17236000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17236000 = ⟨1272112154, 1241602062⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8618000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17694784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17694784 = ⟨191564708, 210936386⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8847392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18284576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18284576 = ⟨825287836, 827623768⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9142288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18612352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18612352 = ⟨71696394, 1142874353⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9306176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19333152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19333152 = ⟨1292135174, 1873761693⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9666576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19791936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19791936 = ⟨1969480937, 1006894505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9895968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20381728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20381728 = ⟨1997455639, 1203807495⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10190864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20447488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20447488 = ⟨737208315, 994408913⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10223744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21430304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21430304 = ⟨1997352534, 256874435⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10715152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21889088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21889088 = ⟨1603510547, 1564100053⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10944544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22478880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22478880 = ⟨524049699, 1622525185⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11239440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22806656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22806656 = ⟨490632219, 1975561253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11403328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23527456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23527456 = ⟨1618300640, 2044189960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11763728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23986240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23986240 = ⟨1425941134, 1127824209⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11993120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24117760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24117760 = ⟨698874721, 1870538774⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12058880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24576032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24576032 = ⟨1891353944, 1439976583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12288016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25624608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25624608 = ⟨2034387724, 135887271⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12812304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26083392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26083392 = ⟨167149823, 694607206⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13041696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26673184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26673184 = ⟨1821458113, 616062148⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13336592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27000960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27000960 = ⟨780080930, 2041308010⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13500480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27721760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27721760 = ⟨1129084215, 128534505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13860880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28180544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28180544 = ⟨1093875284, 2071726454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14090272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28770336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28770336 = ⟨721805450, 597714956⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14385168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28836096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28836096 = ⟨1591600282, 2051756375⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14418048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29818912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29818912 = ⟨14151583, 916493036⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14909456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30277696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30277696 = ⟨1460456122, 625641049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15138848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30867488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30867488 = ⟨96516719, 741579253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15433744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31195264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31195264 = ⟨1177595376, 1360965202⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15597632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31916064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31916064 = ⟨2110757646, 94498554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15958032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32374848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32374848 = ⟨1206462709, 758196898⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16187424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32964640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32964640 = ⟨1226069903, 404085774⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16482320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34472000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34472000 = ⟨1570874064, 1875132980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17236000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35389568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35389568 = ⟨692617514, 121359332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17694784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36569152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36569152 = ⟨589005192, 177638404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18284576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37224704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37224704 = ⟨725159256, 1656881843⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18612352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38666304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38666304 = ⟨512403996, 1930947094⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19333152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39583872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39583872 = ⟨2099089665, 1944305200⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19791936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40763456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40763456 = ⟨30032279, 1907421882⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20381728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40894976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40894976 = ⟨1406739129, 1655035662⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20447488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42860608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42860608 = ⟨1068699855, 877473907⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21430304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43778176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43778176 = ⟨85027212, 1985205185⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21889088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44957760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44957760 = ⟨399743162, 1216469720⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22478880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45613312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45613312 = ⟨752208859, 1818234388⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22806656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47054912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47054912 = ⟨1937460132, 90623575⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23527456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47972480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47972480 = ⟨2109938014, 2101436197⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23986240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48235520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48235520 = ⟨501721213, 24836471⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24117760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49152064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49152064 = ⟨334788124, 1143323060⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24576032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51249216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51249216 = ⟨639566225, 1461702508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25624608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52166784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52166784 = ⟨867501497, 181206828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26083392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53346368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53346368 = ⟨875796590, 1597850054⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26673184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54001920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54001920 = ⟨2104356519, 1209441454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27000960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55443520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55443520 = ⟨2003506275, 920534643⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27721760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56361088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56361088 = ⟨1953187444, 204785335⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28180544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57540672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57540672 = ⟨1771535114, 1332754526⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28770336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57672192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57672192 = ⟨950807070, 1425896716⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28836096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59637824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59637824 = ⟨985358866, 1995143452⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29818912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60555392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60555392 = ⟨307947520, 358641678⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30277696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61734976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61734976 = ⟨152000963, 1441835533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30867488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62390528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62390528 = ⟨760685443, 551088100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31195264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63832128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63832128 = ⟨208502952, 1551330174⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31916064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64749696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64749696 = ⟨1172019519, 119105867⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32374848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65929280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65929280 = ⟨134705655, 1034809964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32964640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_68944000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 68944000 = ⟨726870885, 866179775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34472000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_70779136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70779136 = ⟨1412951400, 1610952524⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35389568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73138304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73138304 = ⟨464966142, 532131267⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36569152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_74449408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 74449408 = ⟨552925513, 839937090⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37224704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77332608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77332608 = ⟨1560646152, 784662533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38666304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_79167744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79167744 = ⟨1095749655, 1051211163⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39583872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_81526912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81526912 = ⟨37805916, 2125912632⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40763456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_81789952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81789952 = ⟨512321057, 1271549173⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40894976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_85721216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 85721216 = ⟨143625435, 1237519179⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42860608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87556352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87556352 = ⟨1352599129, 1650764555⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43778176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89915520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89915520 = ⟨475111329, 1000400298⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44957760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_91226624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 91226624 = ⟨1760484657, 1541398728⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45613312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94109824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94109824 = ⟨205719421, 603487283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47054912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_95944960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 95944960 = ⟨1586457310, 1259772885⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47972480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98304128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98304128 = ⟨234123781, 2077364248⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49152064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102498432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102498432 = ⟨1895156002, 1907681546⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51249216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104333568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104333568 = ⟨1161560196, 53636520⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52166784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106692736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106692736 = ⟨935436242, 156382015⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53346368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108003840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108003840 = ⟨1395919603, 2118643803⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54001920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_110887040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110887040 = ⟨194388875, 774458907⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55443520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_112722176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112722176 = ⟨75291733, 2007910319⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56361088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115081344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115081344 = ⟨1477683978, 685956432⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57540672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115344384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115344384 = ⟨816500702, 1764869715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57672192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_119275648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119275648 = ⟨1570855145, 232786930⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59637824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121110784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121110784 = ⟨1774429086, 320003231⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60555392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123469952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123469952 = ⟨904833534, 647007912⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61734976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124781056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124781056 = ⟨202189478, 1004215588⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62390528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_127664256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 127664256 = ⟨567978009, 863743692⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63832128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_129499392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 129499392 = ⟨1397567215, 2054109794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64749696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_131858560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131858560 = ⟨1031656956, 525471633⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65929280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_137888000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 137888000 = ⟨1325816341, 1798696779⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68944000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_141558272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 141558272 = ⟨747009168, 1321983096⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70779136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_146276608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 146276608 = ⟨919714674, 456477866⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73138304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_148898816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 148898816 = ⟨1556533402, 2005793122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74449408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_154665216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 154665216 = ⟨913207651, 109185651⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77332608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_158335488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 158335488 = ⟨1297434200, 619740071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79167744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_163053824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 163053824 = ⟨1104617942, 605065255⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81526912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_171442432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 171442432 = ⟨897166306, 1605840351⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85721216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_175112704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 175112704 = ⟨1794879715, 1973404495⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87556352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_179831040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 179831040 = ⟨1264491079, 2107669674⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89915520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_182453248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 182453248 = ⟨1484722465, 1078988777⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91226624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_188219648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 188219648 = ⟨1235586835, 151672687⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94109824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_191889920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 191889920 = ⟨1022868566, 1730814515⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_95944960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_196608256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 196608256 = ⟨531356713, 625580458⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98304128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_204996864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 204996864 = ⟨2039791849, 1607786591⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102498432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_208667136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 208667136 = ⟨379986301, 1177973446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104333568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_213385472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 213385472 = ⟨1701324033, 1168190607⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106692736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_216007680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 216007680 = ⟨1988815881, 645751943⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108003840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_221774080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 221774080 = ⟨1035966303, 1312134960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110887040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_225444352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 225444352 = ⟨809826196, 1994179681⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112722176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_230162688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 230162688 = ⟨1689965870, 1468443436⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115081344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_238551296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 238551296 = ⟨81824075, 951888580⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119275648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_242221568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 242221568 = ⟨1029009905, 939134580⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121110784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_246939904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 246939904 = ⟨264598422, 1410624388⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123469952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_249562112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 249562112 = ⟨1513273850, 1722220683⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124781056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_255328512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 255328512 = ⟨1741819205, 1245679229⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_127664256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_258998784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 258998784 = ⟨1764627730, 1593451087⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_129499392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_263717120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 263717120 = ⟨1090484082, 589806413⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131858560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_275776000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 275776000 = ⟨2129738358, 150943141⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_137888000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_283116544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 283116544 = ⟨379559102, 697727211⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_141558272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_292553216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 292553216 = ⟨297539878, 375047638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_146276608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_309330432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 309330432 = ⟨2095330942, 1512738508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_154665216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_316670976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 316670976 = ⟨1358569314, 679273363⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_158335488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_326107648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 326107648 = ⟨1335201193, 628563025⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_163053824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_342884864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 342884864 = ⟨851825413, 964464923⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_171442432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_350225408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 350225408 = ⟨1502308947, 1936338240⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_175112704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_359662080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 359662080 = ⟨1593656526, 30110449⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_179831040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_376439296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 376439296 = ⟨2108150139, 1924410131⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_188219648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_383779840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 383779840 = ⟨1259936220, 2067445894⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_191889920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_393216512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 393216512 = ⟨602228712, 2034184141⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_196608256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_409993728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 409993728 = ⟨679770962, 871637573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_204996864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_417334272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 417334272 = ⟨1694422100, 342104775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_208667136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_426770944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 426770944 = ⟨1627386437, 447174555⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_213385472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_443548160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 443548160 = ⟨974774427, 154536612⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_221774080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_450888704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 450888704 = ⟨277190863, 2137253840⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_225444352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_460325376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 460325376 = ⟨1866802209, 854501938⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_230162688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_477102592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 477102592 = ⟨1243733212, 681881488⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_238551296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_484443136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 484443136 = ⟨675847432, 1010741234⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_242221568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_493879808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 493879808 = ⟨1576740641, 1718011543⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_246939904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_510657024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 510657024 = ⟨1077081423, 1312914084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_255328512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_517997568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 517997568 = ⟨1564688601, 591957108⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_258998784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_527434240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 527434240 = ⟨464603176, 111048140⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_263717120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_551552000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 551552000 = ⟨181714998, 1846973174⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_275776000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_585106432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 585106432 = ⟨24836471, 1645762434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_292553216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_618660864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 618660864 = ⟨1271549173, 1635162590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_309330432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_652215296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 652215296 = ⟨1764869715, 1330982945⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_326107648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_685769728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 685769728 = ⟨2005793122, 590950245⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_342884864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_719324160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 719324160 = ⟨1078988777, 662761182⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_359662080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_752878592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 752878592 = ⟨645751943, 158667766⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_376439296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_786433024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 786433024 = ⟨1722220683, 634209797⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_393216512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_819987456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 819987456 = ⟨697727211, 1767924545⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_409993728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_853541888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 853541888 = ⟨679273363, 788914333⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_426770944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_887096320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 887096320 = ⟨1936338240, 645174700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_443548160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_920650752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 920650752 = ⟨2067445894, 887547427⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_460325376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_954205184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 954205184 = ⟨342104775, 453061547⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_477102592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_987759616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 987759616 = ⟨2137253840, 1870292784⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_493879808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1021314048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1021314048 = ⟨1010741234, 1471636215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_510657024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1054868480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1054868480 = ⟨591957108, 582795046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_527434240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 448) = ⟨300510473, 181714998⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 448 = 14681088 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_14681088

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨300510473, 181714998⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 448) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 449) = ⟨181714998, 1846973174⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 449 = 551552000 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_551552000

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨181714998, 1846973174⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 449) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 450) = ⟨379559102, 697727211⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 450 = 283116544 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_283116544

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨379559102, 697727211⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 450) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 451) = ⟨697727211, 1767924545⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 451 = 819987456 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_819987456

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨697727211, 1767924545⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 451) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 452) = ⟨1556533402, 2005793122⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 452 = 148898816 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_148898816

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1556533402, 2005793122⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 452) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 453) = ⟨2005793122, 590950245⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 453 = 685769728 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_685769728

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2005793122, 590950245⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 453) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 454) = ⟨1694422100, 342104775⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 454 = 417334272 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_417334272

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1694422100, 342104775⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 454) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 455) = ⟨342104775, 453061547⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 455 = 954205184 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_954205184

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨342104775, 453061547⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 455) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 456) = ⟨512321057, 1271549173⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 456 = 81789952 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_81789952

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨512321057, 1271549173⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 456) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 457) = ⟨1271549173, 1635162590⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 457 = 618660864 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_618660864

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1271549173, 1635162590⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 457) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 458) = ⟨1502308947, 1936338240⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 458 = 350225408 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_350225408

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1502308947, 1936338240⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 458) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 459) = ⟨1936338240, 645174700⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 459 = 887096320 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_887096320

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1936338240, 645174700⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 459) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 460) = ⟨1988815881, 645751943⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 460 = 216007680 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_216007680

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1988815881, 645751943⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 460) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 461) = ⟨645751943, 158667766⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 461 = 752878592 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_752878592

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨645751943, 158667766⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 461) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 462) = ⟨675847432, 1010741234⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 462 = 484443136 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_484443136

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨675847432, 1010741234⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 462) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 463) = ⟨1010741234, 1471636215⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 463 = 1021314048 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1021314048

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1010741234, 1471636215⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 463) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 464) = ⟨501721213, 24836471⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 464 = 48235520 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_48235520

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨501721213, 24836471⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 464) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 465) = ⟨24836471, 1645762434⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 465 = 585106432 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_585106432

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨24836471, 1645762434⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 465) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 466) = ⟨1358569314, 679273363⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 466 = 316670976 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_316670976

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1358569314, 679273363⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 466) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 467) = ⟨679273363, 788914333⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 467 = 853541888 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_853541888

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨679273363, 788914333⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 467) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 468) = ⟨1484722465, 1078988777⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 468 = 182453248 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_182453248

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1484722465, 1078988777⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 468) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 469) = ⟨1078988777, 662761182⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 469 = 719324160 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_719324160

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1078988777, 662761182⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 469) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 470) = ⟨277190863, 2137253840⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 470 = 450888704 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_450888704

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨277190863, 2137253840⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 470) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 471) = ⟨2137253840, 1870292784⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 471 = 987759616 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_987759616

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2137253840, 1870292784⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 471) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 472) = ⟨816500702, 1764869715⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 472 = 115344384 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_115344384

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨816500702, 1764869715⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 472) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 473) = ⟨1764869715, 1330982945⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 473 = 652215296 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_652215296

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1764869715, 1330982945⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 473) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 474) = ⟨1259936220, 2067445894⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 474 = 383779840 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_383779840

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1259936220, 2067445894⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 474) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 475) = ⟨2067445894, 887547427⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 475 = 920650752 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_920650752

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2067445894, 887547427⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 475) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 476) = ⟨1513273850, 1722220683⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 476 = 249562112 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_249562112

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1513273850, 1722220683⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 476) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 477) = ⟨1722220683, 634209797⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 477 = 786433024 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_786433024

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1722220683, 634209797⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 477) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 478) = ⟨1564688601, 591957108⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 478 = 517997568 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_517997568

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1564688601, 591957108⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 478) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 479) = ⟨591957108, 582795046⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 479 = 1054868480 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1054868480

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨591957108, 582795046⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 479) := by
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

end R17TableAChunk14Certificate
