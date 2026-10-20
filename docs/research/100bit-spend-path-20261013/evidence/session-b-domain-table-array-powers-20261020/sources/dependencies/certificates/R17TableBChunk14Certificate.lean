import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableBChunk14Certificate
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

theorem power_14336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14336 = ⟨1731306458, 1551812567⟩ := by
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

theorem power_28672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28672 = ⟨1124768046, 299494314⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14336]
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

theorem power_47104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47104 = ⟨496848496, 890027025⟩ := by
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

theorem power_79872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79872 = ⟨1721053354, 1645226881⟩ := by
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

theorem power_94208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94208 = ⟨1753543609, 1294275673⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47104]
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

theorem power_112640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112640 = ⟨983493989, 1661572926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56320]
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

theorem power_145408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 145408 = ⟨477007636, 1158627154⟩ := by
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

theorem power_159744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 159744 = ⟨1924483244, 1528988896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79872]
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

theorem power_178176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 178176 = ⟨942015741, 884128330⟩ := by
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

theorem power_210944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 210944 = ⟨1583620585, 920603234⟩ := by
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

theorem power_225280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 225280 = ⟨122809504, 181977862⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112640]
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

theorem power_243712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 243712 = ⟨894328797, 399061936⟩ := by
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

theorem power_276480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 276480 = ⟨937246950, 1944723122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_138240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_285696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 285696 = ⟨369514396, 980205573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_142848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_290816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 290816 = ⟨1458581325, 1279621404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_145408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_302080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 302080 = ⟨194008892, 454794782⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_151040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_309248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 309248 = ⟨830880001, 1851760075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_154624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_318464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 318464 = ⟨178740611, 2113243823⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_159232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_334848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 334848 = ⟨199001272, 1665021225⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_167424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_342016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 342016 = ⟨1790471539, 839403197⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_171008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_351232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 351232 = ⟨1161610822, 947748647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_175616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_356352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 356352 = ⟨128738146, 457848703⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_178176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_367616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 367616 = ⟨1816510680, 2042381711⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_183808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_374784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 374784 = ⟨202323676, 882237532⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_187392]
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

theorem power_407552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 407552 = ⟨1102747704, 1680525000⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_203776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_416768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 416768 = ⟨754407186, 1989571461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_208384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_421888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 421888 = ⟨1212320872, 1495300507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_210944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_433152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 433152 = ⟨287842196, 1085363673⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_216576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_440320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 440320 = ⟨411614884, 176236651⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_220160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_449536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 449536 = ⟨1331287229, 1368413357⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_224768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_465920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 465920 = ⟨394776767, 1670648596⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_232960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_473088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 473088 = ⟨1645824567, 173000716⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_236544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_482304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 482304 = ⟨1390582301, 22370994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_241152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_487424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 487424 = ⟨1300871249, 1490001285⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_243712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_498688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 498688 = ⟨1894947366, 1922894643⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_249344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_505856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 505856 = ⟨1624712612, 1864287004⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_252928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_515072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 515072 = ⟨1722960484, 1950506513⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_257536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_538624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 538624 = ⟨521614553, 1525484332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_269312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_552960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 552960 = ⟨333636023, 948573238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_276480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_571392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 571392 = ⟨439036667, 258250822⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_285696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_604160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 604160 = ⟨1418366884, 1964008531⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_302080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_618496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 618496 = ⟨1573749961, 753946855⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_309248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_636928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 636928 = ⟨1072358646, 22599558⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_318464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_669696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 669696 = ⟨1682918895, 1192974263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_334848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_684032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 684032 = ⟨841695573, 113926739⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_342016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_702464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 702464 = ⟨1470626692, 1656147731⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_351232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_735232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 735232 = ⟨1117070175, 1259619453⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_367616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_749568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 749568 = ⟨895013455, 284231781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_374784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_768000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 768000 = ⟨184729068, 206592744⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_384000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_800768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 800768 = ⟨1239129346, 388416094⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_400384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_815104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 815104 = ⟨994459063, 1883501554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_407552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_833536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 833536 = ⟨1145720356, 1705271835⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_416768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_866304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 866304 = ⟨417580301, 1996323446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_433152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_880640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 880640 = ⟨1104635206, 858881536⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_440320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_899072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 899072 = ⟨1724475994, 113652685⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_449536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_931840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 931840 = ⟨1408801601, 296320982⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_465920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_946176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 946176 = ⟨1994468584, 1611997849⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_473088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_964608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 964608 = ⟨55417806, 712427814⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_482304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_997376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 997376 = ⟨1621634668, 248117407⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_498688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1011712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1011712 = ⟨277472845, 620479805⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_505856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1030144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1030144 = ⟨371600365, 1215100652⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_515072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1077248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1077248 = ⟨1055409021, 1215994438⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_538624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1142784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1142784 = ⟨1908790330, 386453773⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_571392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1208320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1208320 = ⟨176039723, 154417691⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_604160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1273856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1273856 = ⟨617875881, 1291144021⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_636928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1339392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1339392 = ⟨1873772561, 1110881047⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_669696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1404928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1404928 = ⟨582395095, 1653762059⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_702464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1470464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1470464 = ⟨540487422, 1063443989⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_735232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1536000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1536000 = ⟨454136966, 941654637⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_768000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1601536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1601536 = ⟨548067276, 713948312⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_800768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1667072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1667072 = ⟨305276529, 1041544704⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_833536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1732608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1732608 = ⟨52691895, 801280851⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_866304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1798144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1798144 = ⟨1880738855, 621634671⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_899072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1863680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1863680 = ⟨308028775, 1118600221⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_931840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1929216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1929216 = ⟨1504303166, 365743328⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_964608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1994752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1994752 = ⟨2119188567, 919124989⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_997376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2060288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2060288 = ⟨594888648, 735387713⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1030144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 448) = ⟨1124768046, 299494314⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 448 = 28672 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_28672

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1124768046, 299494314⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 448) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 449) = ⟨1055409021, 1215994438⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 449 = 1077248 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1077248

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1055409021, 1215994438⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 449) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 450) = ⟨333636023, 948573238⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 450 = 552960 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_552960

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨333636023, 948573238⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 450) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 451) = ⟨548067276, 713948312⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 451 = 1601536 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1601536

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨548067276, 713948312⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 451) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 452) = ⟨1458581325, 1279621404⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 452 = 290816 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_290816

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1458581325, 1279621404⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 452) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 453) = ⟨1873772561, 1110881047⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 453 = 1339392 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1339392

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1873772561, 1110881047⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 453) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 454) = ⟨994459063, 1883501554⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 454 = 815104 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_815104

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨994459063, 1883501554⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 454) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 455) = ⟨308028775, 1118600221⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 455 = 1863680 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1863680

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨308028775, 1118600221⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 455) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 456) = ⟨1924483244, 1528988896⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 456 = 159744 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_159744

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1924483244, 1528988896⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 456) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 457) = ⟨176039723, 154417691⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 457 = 1208320 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1208320

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨176039723, 154417691⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 457) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 458) = ⟨841695573, 113926739⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 458 = 684032 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_684032

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨841695573, 113926739⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 458) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 459) = ⟨52691895, 801280851⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 459 = 1732608 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1732608

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨52691895, 801280851⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 459) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 460) = ⟨1212320872, 1495300507⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 460 = 421888 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_421888

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1212320872, 1495300507⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 460) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 461) = ⟨540487422, 1063443989⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 461 = 1470464 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1470464

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨540487422, 1063443989⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 461) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 462) = ⟨1994468584, 1611997849⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 462 = 946176 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_946176

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1994468584, 1611997849⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 462) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 463) = ⟨2119188567, 919124989⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 463 = 1994752 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1994752

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2119188567, 919124989⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 463) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 464) = ⟨1753543609, 1294275673⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 464 = 94208 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_94208

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1753543609, 1294275673⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 464) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 465) = ⟨1908790330, 386453773⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 465 = 1142784 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1142784

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1908790330, 386453773⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 465) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 466) = ⟨1573749961, 753946855⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 466 = 618496 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_618496

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1573749961, 753946855⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 466) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 467) = ⟨305276529, 1041544704⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 467 = 1667072 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1667072

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨305276529, 1041544704⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 467) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 468) = ⟨128738146, 457848703⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 468 = 356352 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_356352

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨128738146, 457848703⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 468) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 469) = ⟨582395095, 1653762059⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 469 = 1404928 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1404928

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨582395095, 1653762059⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 469) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 470) = ⟨1104635206, 858881536⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 470 = 880640 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_880640

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1104635206, 858881536⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 470) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 471) = ⟨1504303166, 365743328⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 471 = 1929216 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1929216

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1504303166, 365743328⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 471) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 472) = ⟨122809504, 181977862⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 472 = 225280 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_225280

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨122809504, 181977862⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 472) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 473) = ⟨617875881, 1291144021⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 473 = 1273856 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1273856

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨617875881, 1291144021⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 473) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 474) = ⟨895013455, 284231781⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 474 = 749568 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_749568

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨895013455, 284231781⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 474) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 475) = ⟨1880738855, 621634671⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 475 = 1798144 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1798144

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1880738855, 621634671⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 475) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 476) = ⟨1300871249, 1490001285⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 476 = 487424 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_487424

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1300871249, 1490001285⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 476) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 477) = ⟨454136966, 941654637⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 477 = 1536000 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1536000

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨454136966, 941654637⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 477) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 478) = ⟨277472845, 620479805⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 478 = 1011712 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1011712

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨277472845, 620479805⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 478) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 479) = ⟨594888648, 735387713⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 479 = 2060288 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2060288

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨594888648, 735387713⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 479) := by
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

end R17TableBChunk14Certificate
