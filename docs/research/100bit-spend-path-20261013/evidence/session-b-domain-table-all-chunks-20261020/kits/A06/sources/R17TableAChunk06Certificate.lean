import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk06Certificate
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

theorem power_70 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70 = ⟨115184242, 829081638⟩ := by
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

theorem power_76 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76 = ⟨2095288830, 1138360406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77 = ⟨1255986648, 1483159588⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38]
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

theorem power_93 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93 = ⟨1406255700, 949804171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_96 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96 = ⟨1827909629, 1836816527⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48]
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

theorem power_109 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109 = ⟨584812917, 431696491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54]
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

theorem power_134 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 134 = ⟨445214781, 1346295538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_139 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 139 = ⟨1724704064, 760534735⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_140 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 140 = ⟨166789141, 776909418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_147 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 147 = ⟨1871749785, 872210914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73]
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

theorem power_155 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 155 = ⟨95599379, 1884941993⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_163 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 163 = ⟨1027654423, 1354925944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_166 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 166 = ⟨1545644833, 1423557268⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_171 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 171 = ⟨617956980, 1693803782⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85]
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

theorem power_179 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 179 = ⟨64917534, 1646995590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_182 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 182 = ⟨2049618010, 1067206337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_187 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 187 = ⟨799610937, 665210564⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 192 = ⟨1343082982, 1656388718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_195 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 195 = ⟨1952223760, 1817980554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_97]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_198 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 198 = ⟨1388304776, 536803269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_203 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 203 = ⟨1626325386, 533448899⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_204 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 204 = ⟨349974108, 1382066042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_211 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 211 = ⟨2040897111, 1468235903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105]
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

theorem power_219 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 219 = ⟨742915033, 302287293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_227 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 227 = ⟨881338165, 1738354347⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_113]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_230 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 230 = ⟨1382570788, 293157249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_235 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 235 = ⟨1800142309, 2130869144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_236 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 236 = ⟨1882349838, 1929949081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_243 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 243 = ⟨1155190479, 56664675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_246 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 246 = ⟨1542475593, 236234992⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_251 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 251 = ⟨1126878156, 83731982⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_262 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 262 = ⟨287814896, 309376222⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_268 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 268 = ⟨2013245287, 307235301⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_134]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_278 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 278 = ⟨2075577012, 158471336⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_139]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 280 = ⟨1151293179, 2142156513⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_140]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_294 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 294 = ⟨1162279362, 654843129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_147]
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

theorem power_310 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 310 = ⟨1522755374, 386473027⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_155]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_326 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 326 = ⟨1727516045, 379603300⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_163]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_332 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 332 = ⟨1776824621, 1228552608⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_166]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_342 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 342 = ⟨1980366618, 934891035⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_171]
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

theorem power_358 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 358 = ⟨1922001538, 34318354⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_179]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_364 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 364 = ⟨658152473, 1072395370⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_182]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_374 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 374 = ⟨2056754104, 1797437257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_187]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 384 = ⟨1594705154, 1156423391⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_390 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 390 = ⟨1899796831, 2026834283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_195]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_396 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 396 = ⟨1317899525, 1413993072⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_198]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_406 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 406 = ⟨1993180049, 1487749769⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_203]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 408 = ⟨869725335, 1982977009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_204]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_422 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 422 = ⟨1600319089, 638267598⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_211]
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

theorem power_438 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 438 = ⟨585484066, 1561821963⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_219]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_454 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 454 = ⟨398508878, 772378678⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_227]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_460 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 460 = ⟨1702972884, 206156245⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_230]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_470 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 470 = ⟨266031331, 1924825944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_235]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 472 = ⟨1631040737, 1802692420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_236]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_486 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 486 = ⟨2035251788, 668739766⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_243]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_492 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 492 = ⟨1391406444, 1044822016⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_246]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_502 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 502 = ⟨1490553968, 258980480⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_251]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_524 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 524 = ⟨111014593, 775991579⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_262]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 536 = ⟨868141221, 1752893379⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_268]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_556 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 556 = ⟨268812888, 841508424⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_278]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 560 = ⟨1279482299, 2145341211⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_588 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 588 = ⟨109266760, 756306898⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_294]
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

theorem power_620 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 620 = ⟨1678507858, 1723938487⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_310]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_652 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 652 = ⟨1944837628, 360321126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_326]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 664 = ⟨1497739154, 867480608⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_332]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_684 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 684 = ⟨633764744, 1139409834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_342]
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

theorem power_716 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 716 = ⟨807928024, 181072667⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_358]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 728 = ⟨152082636, 622063853⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_364]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_748 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 748 = ⟨1533866668, 2042313092⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_374]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 768 = ⟨784830374, 912241638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_780 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 780 = ⟨87005563, 1490211751⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_390]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 792 = ⟨1120617728, 1601145033⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_396]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_812 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 812 = ⟨674748761, 1180944676⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_406]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 816 = ⟨709216745, 661921156⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_844 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 844 = ⟨593422479, 1594591533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_422]
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

theorem power_876 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 876 = ⟨1585126802, 1483382865⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_438]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_908 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 908 = ⟨617654397, 899431913⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_454]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 920 = ⟨1067422211, 221235944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_460]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_940 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 940 = ⟨869208073, 769182738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_470]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 944 = ⟨144926793, 2141311607⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_972 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 972 = ⟨10090051, 2036818165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_486]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 984 = ⟨2061938011, 1225693194⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_492]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1004 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1004 = ⟨1988779399, 1219292293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_502]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1048 = ⟨1720061523, 273173875⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_524]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1072 = ⟨171097394, 1990602842⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1112 = ⟨1509285423, 1110052489⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_556]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1120 = ⟨428562734, 499127922⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1176 = ⟨1337701156, 1198522828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_588]
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

theorem power_1240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1240 = ⟨465988776, 186828766⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_620]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1304 = ⟨1010903847, 1858789625⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_652]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1328 = ⟨1052768950, 700500903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1368 = ⟨1514395361, 2134321615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_684]
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

theorem power_1432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1432 = ⟨725452484, 1460220640⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_716]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1456 = ⟨447640678, 314692891⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1496 = ⟨1626198703, 429410477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_748]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1536 = ⟨999230472, 1852479283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1560 = ⟨180884883, 538544345⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_780]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1584 = ⟨1189594089, 370965434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1624 = ⟨1926365772, 1981066635⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_812]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1632 = ⟨1906266428, 2062433102⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1688 = ⟨1792732, 1461195162⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_844]
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

theorem power_1752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1752 = ⟨1458004538, 239986594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_876]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1816 = ⟨1496711142, 760017225⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_908]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1840 = ⟨423791970, 467357182⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1880 = ⟨890167323, 687452307⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_940]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1888 = ⟨269305067, 1242485321⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1944 = ⟨301407602, 544320134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_972]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1968 = ⟨1305669901, 1881194309⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2008 = ⟨855514728, 1815742830⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1004]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2096 = ⟨1805567046, 1238639368⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2144 = ⟨945143520, 979357515⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2224 = ⟨1745525696, 769760567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2240 = ⟨1882985882, 1884234849⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2352 = ⟨993805021, 453742291⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1176]
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

theorem power_2480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2480 = ⟨1879715677, 2055657011⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2608 = ⟨719500070, 1210398088⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2656 = ⟨800991336, 1543881133⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2736 = ⟨1133836227, 2057567625⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1368]
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

theorem power_2864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2864 = ⟨1307210844, 551960889⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2912 = ⟨1514720099, 1344022831⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2992 = ⟨497029902, 1283766712⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3072 = ⟨2054061671, 949045631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3120 = ⟨1758715157, 1514085173⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3168 = ⟨1868814331, 1048694373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3248 = ⟨929654382, 1189184447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3264 = ⟨1045835668, 1112919339⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3376 = ⟨357492176, 1415561852⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1688]
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

theorem power_3504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3504 = ⟨985269965, 309158862⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3632 = ⟨1047159439, 407909775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3680 = ⟨993162928, 1170744481⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3760 = ⟨373501011, 1773718357⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3776 = ⟨1759380646, 1693051226⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3888 = ⟨2009665362, 160281151⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3936 = ⟨993869978, 1660964583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4016 = ⟨479859971, 232817279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4192 = ⟨1992224877, 531446035⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4288 = ⟨1337526504, 177086970⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4448 = ⟨1017551858, 1236182754⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4480 = ⟨148358476, 1302044281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4704 = ⟨1156626838, 1971946255⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2352]
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

theorem power_4960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4960 = ⟨2083665654, 991547815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5216 = ⟨631832940, 1214254297⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5312 = ⟨85906648, 1487213051⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5472 = ⟨1038155407, 654032931⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2736]
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

theorem power_5728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5728 = ⟨1761772800, 2128352543⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5824 = ⟨1240031076, 1183521928⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5984 = ⟨193776427, 193013472⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6144 = ⟨1121167, 714917308⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6240 = ⟨717869903, 1082344630⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6336 = ⟨445780260, 1075905986⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6496 = ⟨376013865, 14021834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6528 = ⟨491178846, 571176726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6752 = ⟨2033433106, 1697992958⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3376]
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

theorem power_7008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7008 = ⟨1107806556, 337654334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7264 = ⟨1301964685, 1220505582⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7360 = ⟨508470430, 979783914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7520 = ⟨100383435, 1123913136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7552 = ⟨198166676, 739745441⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7776 = ⟨2005898533, 1148783894⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7872 = ⟨1647829762, 864777955⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8032 = ⟨1869824360, 2007729881⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8384 = ⟨1535339787, 998251690⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8576 = ⟨42830196, 2016881506⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8896 = ⟨1395128231, 1865727046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8960 = ⟨2091181541, 1615031214⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9408 = ⟨701979544, 793605973⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4704]
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

theorem power_9920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9920 = ⟨416032040, 436061717⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10432 = ⟨1197290255, 742207427⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10624 = ⟨127257755, 138520870⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10944 = ⟨1989420027, 796334698⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5472]
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

theorem power_11456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11456 = ⟨1585333377, 1083459370⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11648 = ⟨1954706102, 753082980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11968 = ⟨379588099, 2015219960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12289 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12289 = ⟨1678169707, 1195898523⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12480 = ⟨1972242062, 2100691631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12672 = ⟨1198757226, 2146773352⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12992 = ⟨2073155059, 1861723544⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13056 = ⟨1464918947, 1524839126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13504 = ⟨1113330667, 1443829141⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6752]
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

theorem power_14016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14016 = ⟨1727218271, 1378950967⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14528 = ⟨19301632, 1568711984⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14720 = ⟨312458750, 1882679726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15040 = ⟨21654848, 1835385374⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15104 = ⟨1798126249, 1236021248⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15552 = ⟨399467380, 1186469564⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15744 = ⟨1326215179, 1403584070⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16064 = ⟨1247842032, 2066924212⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16768 = ⟨910395628, 1014731513⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17152 = ⟨121948857, 1429064166⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17792 = ⟨1224155440, 737054196⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17920 = ⟨1517789543, 430872700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18816 = ⟨1871025797, 143060818⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9408]
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

theorem power_19840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19840 = ⟨65328010, 639240918⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20864 = ⟨968705731, 523606027⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21248 = ⟨349237010, 541976007⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21888 = ⟨1648413638, 1061699244⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10944]
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

theorem power_22912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22912 = ⟨103117915, 535771622⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23296 = ⟨479665279, 2094867031⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23936 = ⟨419971577, 335850108⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24578 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24578 = ⟨1300987963, 2099206259⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12289]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24960 = ⟨2069000364, 1177274294⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25344 = ⟨279340041, 1266969425⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25984 = ⟨314467329, 1076108506⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26112 = ⟨733299889, 1597634788⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27008 = ⟨1102569727, 1832459335⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13504]
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

theorem power_28032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28032 = ⟨817446573, 1865300049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29056 = ⟨37178198, 395454790⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29440 = ⟨309688732, 1590447564⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30080 = ⟨793102838, 1371236975⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30208 = ⟨422667070, 645353689⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31104 = ⟨827426978, 515986394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31488 = ⟨1506146295, 15201801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32128 = ⟨1577983544, 1968787947⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33536 = ⟨931754353, 2107482589⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34304 = ⟨1651788202, 1051285238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35584 = ⟨1896519407, 1492919974⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35840 = ⟨1055573105, 1574974366⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37632 = ⟨1807268646, 1387828925⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18816]
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

theorem power_39680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39680 = ⟨1903571649, 1433527792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41728 = ⟨2131871458, 1563536626⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42496 = ⟨1607105031, 64991137⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43776 = ⟨1363012592, 1582066627⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44032 = ⟨1331567834, 835563095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45057 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45057 = ⟨1534324197, 1799324692⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45824 = ⟨922242157, 135837518⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46592 = ⟨1589750714, 89434798⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47872 = ⟨787168508, 926614792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49156 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49156 = ⟨1519318993, 1466054195⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24578]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49920 = ⟨1026503271, 1969366019⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50688 = ⟨165344061, 601375750⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51968 = ⟨2123816611, 1161003328⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52224 = ⟨1934269047, 1171518634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54016 = ⟨605949269, 1961649522⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27008]
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

theorem power_56064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56064 = ⟨802977795, 1098240563⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58112 = ⟨441624130, 1330097580⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58880 = ⟨705468968, 307830817⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60160 = ⟨1187724674, 1065852279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60416 = ⟨173326764, 1317620144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62208 = ⟨753028638, 1902965361⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62976 = ⟨513154727, 1233224454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64256 = ⟨1838928993, 2087714324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_67072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67072 = ⟨111102438, 798571083⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_68608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 68608 = ⟨368688812, 1406464750⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71168 = ⟨184241407, 1379835763⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71680 = ⟨545041803, 1880690526⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_75264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 75264 = ⟨1546705477, 1945124534⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76800 = ⟨1291436019, 379698066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77825 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77825 = ⟨495677072, 1045938530⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_79360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79360 = ⟨891168903, 1145658271⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_83456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83456 = ⟨2102874441, 812132678⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_84992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84992 = ⟨231535418, 394352870⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87552 = ⟨986053408, 1438909564⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88064 = ⟨1629336806, 1209471979⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90114 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90114 = ⟨1347296307, 1969743965⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45057]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_91648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 91648 = ⟨2067304729, 670477447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_93184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93184 = ⟨2140616907, 88929576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_95744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 95744 = ⟨1287895149, 733680821⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98312 = ⟨530925981, 724318659⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49156]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_99840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 99840 = ⟨2113594819, 1650213185⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_101376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101376 = ⟨1803958918, 1911609679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_103936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103936 = ⟨866756571, 1940004712⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104448 = ⟨2007972020, 427573065⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108032 = ⟨631069069, 1073533423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_109568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109568 = ⟨1845927943, 1778670715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_110593 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110593 = ⟨941711877, 1943860534⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_112128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112128 = ⟨1386244047, 812565330⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_116224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116224 = ⟨928441304, 687611144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_117760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117760 = ⟨2093537614, 1504172109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120320 = ⟨875923454, 1002878540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120832 = ⟨947160035, 834918877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124416 = ⟨1226236584, 810920020⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125952 = ⟨895303357, 1473739262⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_128512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128512 = ⟨721805400, 1392862222⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_134144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 134144 = ⟨1388404629, 1554667997⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_137216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 137216 = ⟨1757625041, 2055518664⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_142336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 142336 = ⟨4665041, 1024239759⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_143361 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 143361 = ⟨770028965, 155230776⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_150528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 150528 = ⟨1556071938, 630300633⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_153600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 153600 = ⟨1507456974, 2049594119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_155650 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 155650 = ⟨1306766838, 1578982443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77825]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_158720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 158720 = ⟨70447031, 2045853490⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_166912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 166912 = ⟨1012144713, 1307005340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_169984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 169984 = ⟨1644701032, 1157789670⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_175104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 175104 = ⟨556319643, 929512182⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_176129 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 176129 = ⟨1849975383, 1132095232⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_180228 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 180228 = ⟨153225766, 1312299489⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90114]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_183296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 183296 = ⟨328747162, 1067452003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_186368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 186368 = ⟨1787064488, 51350066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_191488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 191488 = ⟨1105783134, 1665513152⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_95744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_196624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 196624 = ⟨247439041, 1910962901⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_199680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 199680 = ⟨1914752554, 333151223⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_202752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 202752 = ⟨1610082685, 851242621⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_207872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 207872 = ⟨1209995250, 553854041⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_208897 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 208897 = ⟨620960944, 1739383477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_216064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 216064 = ⟨111550904, 20507232⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_219136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 219136 = ⟨232802090, 2145208109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_221186 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 221186 = ⟨1725834531, 1877520909⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110593]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_224256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 224256 = ⟨2086473419, 1632839764⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_232448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 232448 = ⟨262887954, 1505590050⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_235520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 235520 = ⟨402089960, 1847126256⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_240640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 240640 = ⟨963307978, 1053907585⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_241665 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 241665 = ⟨1945490561, 860316274⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_248832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 248832 = ⟨1855084989, 994327263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_251904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 251904 = ⟨2044929748, 722179404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_257024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 257024 = ⟨1291854463, 1462274122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_268288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 268288 = ⟨1471522468, 1477107841⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_134144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_274433 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 274433 = ⟨1881671972, 348034253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_137216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_284672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 284672 = ⟨16505965, 987006001⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_142336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_286722 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 286722 = ⟨420722843, 1099363270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_143361]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_301056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 301056 = ⟨112183282, 231347201⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_150528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_307201 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 307201 = ⟨868671784, 1224077712⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_153600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_311300 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 311300 = ⟨1203754327, 1405838204⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_155650]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_317440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 317440 = ⟨2016210977, 309319334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_158720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_333824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 333824 = ⟨773058927, 1649374996⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_166912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_339969 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 339969 = ⟨2044765585, 2092621273⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_169984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_350208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 350208 = ⟨1761157983, 1349037604⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_175104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_352258 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 352258 = ⟨234409535, 1079016645⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_176129]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_360456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 360456 = ⟨1045143612, 1469759652⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_180228]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_366592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 366592 = ⟨1424871099, 1797932349⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_183296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_372737 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 372737 = ⟨1065926454, 140986407⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_186368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_382976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 382976 = ⟨1511581357, 1880607053⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_191488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_393248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 393248 = ⟨1212657198, 200978407⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_196624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_399360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 399360 = ⟨2090085646, 1554994065⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_199680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_405505 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 405505 = ⟨1380305974, 1172231178⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_202752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_415744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 415744 = ⟨1283093627, 1257551079⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_207872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_417794 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 417794 = ⟨873827153, 1031949956⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_208897]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_432128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 432128 = ⟨1053998608, 1658727485⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_216064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_438273 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 438273 = ⟨1646468927, 1254156049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_219136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_442372 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 442372 = ⟨1233477379, 998489453⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_221186]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_448512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 448512 = ⟨1113246356, 1550960305⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_224256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_464896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 464896 = ⟨592408453, 1788732980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_232448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_471041 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 471041 = ⟨465199972, 1548317276⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_235520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_481280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 481280 = ⟨2098579920, 1448151653⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_240640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_483330 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 483330 = ⟨2092627443, 538657618⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_241665]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_497664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 497664 = ⟨219827766, 611239734⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_248832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_503809 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 503809 = ⟨2051550901, 708895215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_251904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_514048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 514048 = ⟨837830915, 726127712⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_257024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_536577 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 536577 = ⟨1565477713, 755508710⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_268288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_548866 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 548866 = ⟨2075349801, 1081786914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_274433]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_569345 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 569345 = ⟨654582190, 1337771087⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_284672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_573444 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 573444 = ⟨1846921725, 1290320400⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_286722]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_602113 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 602113 = ⟨125751229, 254069929⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_301056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_614402 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 614402 = ⟨699534683, 1698779920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_307201]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_622600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 622600 = ⟨1739040634, 12763894⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_311300]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_634881 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 634881 = ⟨156676630, 519001859⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_317440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_667649 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 667649 = ⟨1165269572, 1791880220⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_333824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_679938 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 679938 = ⟨1572929239, 2029004278⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_339969]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_700417 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 700417 = ⟨1799751845, 667898171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_350208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_704516 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 704516 = ⟨1333772811, 2116343155⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_352258]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_720912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 720912 = ⟨1804139504, 649378862⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_360456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_733185 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 733185 = ⟨1649445136, 1483652089⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_366592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_745474 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 745474 = ⟨1467325288, 218382863⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_372737]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_765953 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 765953 = ⟨1565714337, 1179449328⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_382976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_786496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 786496 = ⟨967751863, 618572701⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_393248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_798721 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 798721 = ⟨335529963, 310979519⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_399360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_811010 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 811010 = ⟨164060721, 723982099⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_405505]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_831489 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 831489 = ⟨590962790, 1043444241⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_415744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_835588 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 835588 = ⟨1217997029, 560962554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_417794]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_864257 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 864257 = ⟨809749420, 1593693794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_432128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_876546 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 876546 = ⟨747652601, 674119726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_438273]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_884744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 884744 = ⟨2033699519, 1833803966⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_442372]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_897025 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 897025 = ⟨867034082, 1563571818⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_448512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_929793 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 929793 = ⟨440043090, 1642492810⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_464896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_942082 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 942082 = ⟨1674600653, 629162213⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_471041]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_962561 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 962561 = ⟨1212525977, 499030854⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_481280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_966660 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 966660 = ⟨1709483145, 609705657⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_483330]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_995329 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 995329 = ⟨1158350923, 1144184323⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_497664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1007618 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1007618 = ⟨240032622, 1142732410⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_503809]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1028097 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1028097 = ⟨1798010345, 14813101⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_514048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1073154 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1073154 = ⟨1616376931, 116941228⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_536577]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1097732 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1097732 = ⟨130709310, 1700844317⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_548866]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1138690 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1138690 = ⟨1132834263, 1951098566⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_569345]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1146888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1146888 = ⟨454915539, 1125585540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_573444]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1204226 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1204226 = ⟨2048859078, 359761799⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_602113]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1228804 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1228804 = ⟨229035304, 51919207⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_614402]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1245200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1245200 = ⟨1566189192, 640562798⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_622600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1269762 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1269762 = ⟨1588726605, 1454026865⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_634881]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1335298 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1335298 = ⟨1888224562, 46118940⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_667649]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1359876 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1359876 = ⟨1974852543, 215848032⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_679938]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1400834 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1400834 = ⟨81522237, 1196462590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_700417]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1409032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1409032 = ⟨717078277, 158853866⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_704516]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1441824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1441824 = ⟨1116746141, 567020875⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_720912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1466370 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1466370 = ⟨2110475032, 981522628⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_733185]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1490948 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1490948 = ⟨777177888, 1626573664⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_745474]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1531906 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1531906 = ⟨1703232274, 1887823157⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_765953]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1572992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1572992 = ⟨1813265317, 565314330⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_786496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1597442 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1597442 = ⟨248660068, 1344671767⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_798721]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1622020 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1622020 = ⟨187337293, 1980413330⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_811010]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1662978 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1662978 = ⟨2127840806, 1760793821⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_831489]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1671176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1671176 = ⟨1121895484, 1764540651⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_835588]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1728514 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1728514 = ⟨545943666, 1980137602⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_864257]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1753092 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1753092 = ⟨1703411154, 944506266⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_876546]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1769488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1769488 = ⟨2128550983, 405520486⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_884744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1794050 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1794050 = ⟨1448616622, 732776983⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_897025]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1859586 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1859586 = ⟨570664750, 54370729⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_929793]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1884164 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1884164 = ⟨455088706, 212872368⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_942082]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1925122 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1925122 = ⟨100752726, 1627719304⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_962561]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1933320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1933320 = ⟨1372093128, 1145315373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_966660]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1990658 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1990658 = ⟨334059450, 528670386⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_995329]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2015236 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2015236 = ⟨1040157459, 1731624235⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1007618]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2056194 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2056194 = ⟨1688144872, 1779341628⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1028097]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2146308 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2146308 = ⟨439751323, 1269928396⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1073154]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2195464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2195464 = ⟨330838174, 1799783839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1097732]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2277380 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2277380 = ⟨169971796, 670831808⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1138690]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2293776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2293776 = ⟨1603141834, 1430899551⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1146888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2408452 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2408452 = ⟨1391813450, 1171322233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1204226]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2457608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2457608 = ⟨192651922, 733864601⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1228804]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2490400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2490400 = ⟨1661194103, 843803633⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1245200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2539524 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2539524 = ⟨323246803, 657958697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1269762]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2670596 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2670596 = ⟨595673102, 1938458812⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1335298]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2719752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2719752 = ⟨1978376502, 1978222931⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1359876]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2801668 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2801668 = ⟨1149593246, 165147991⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1400834]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2818064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2818064 = ⟨476064118, 2064588209⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1409032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2883648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2883648 = ⟨1639292868, 1424332548⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1441824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2932740 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2932740 = ⟨862898071, 419494260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1466370]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2981896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2981896 = ⟨618592024, 194613229⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1490948]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3063812 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3063812 = ⟨227969972, 375231321⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1531906]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3145984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3145984 = ⟨1709129828, 568133576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1572992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3194884 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3194884 = ⟨1274215681, 571716357⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1597442]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3244040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3244040 = ⟨367587874, 1119022885⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1622020]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3325956 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3325956 = ⟨1336422287, 1203549334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1662978]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3342352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3342352 = ⟨47601727, 98206420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1671176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3457028 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3457028 = ⟨1763934574, 375832940⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1728514]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3506184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3506184 = ⟨1734072989, 1703357728⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1753092]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3538976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3538976 = ⟨1361363075, 1140420221⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1769488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3588100 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3588100 = ⟨2099426074, 100390084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1794050]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3719172 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3719172 = ⟨848689757, 1119847416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1859586]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3768328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3768328 = ⟨165812297, 625703653⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1884164]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3850244 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3850244 = ⟨1240953678, 1279901070⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1925122]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3866640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3866640 = ⟨793273162, 816397029⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1933320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3981316 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3981316 = ⟨1534706976, 324686953⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1990658]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4030472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4030472 = ⟨249455687, 1000952595⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2015236]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4112388 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4112388 = ⟨867046644, 1525105710⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2056194]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4292616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4292616 = ⟨943222910, 848778263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2146308]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4390928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4390928 = ⟨1187688956, 751189037⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2195464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4554760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4554760 = ⟨799524307, 882506084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2277380]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4587552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4587552 = ⟨651955251, 925874326⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2293776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4816904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4816904 = ⟨534060562, 851634867⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2408452]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4915216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4915216 = ⟨1495377215, 608124290⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2457608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4980800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4980800 = ⟨923212980, 1982054809⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2490400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5079048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5079048 = ⟨1785655999, 920439295⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2539524]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5341192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5341192 = ⟨2012767388, 1561726518⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2670596]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5439504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5439504 = ⟨1318508475, 38268077⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2719752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5603336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5603336 = ⟨1006183206, 1828988066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2801668]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5636128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5636128 = ⟨1795340682, 2093061262⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2818064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5767296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5767296 = ⟨1122413527, 1181424704⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2883648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5865480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5865480 = ⟨1075151866, 784379207⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2932740]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5963792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5963792 = ⟨226263872, 1312890073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2981896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6127624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6127624 = ⟨423393280, 1285912889⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3063812]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6291968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6291968 = ⟨1862007840, 216597697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3145984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6389768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6389768 = ⟨637472649, 1071890183⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3194884]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6488080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6488080 = ⟨885573580, 529462599⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3244040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6651912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6651912 = ⟨1345360676, 1632257830⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3325956]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6684704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6684704 = ⟨1201599075, 640717606⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3342352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6914056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6914056 = ⟨1874897643, 1871844260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3457028]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7012368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7012368 = ⟨528987152, 962534626⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3506184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7077952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7077952 = ⟨505062008, 978930826⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3538976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7176200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7176200 = ⟨1561746358, 1517578726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3588100]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7438344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7438344 = ⟨439566904, 1079528518⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3719172]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7536656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7536656 = ⟨199900977, 137192595⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3768328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7700488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7700488 = ⟨912429904, 1500260551⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3850244]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7733280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7733280 = ⟨2066957947, 1613134724⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3866640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7962632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7962632 = ⟨1658042434, 1768552104⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3981316]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8060944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8060944 = ⟨810248200, 396576649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4030472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8224776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8224776 = ⟨344546310, 930133129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4112388]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8585232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8585232 = ⟨1115681449, 1024191886⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4292616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8781856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8781856 = ⟨690669420, 168252060⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4390928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9109520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9109520 = ⟨2077030957, 1866988123⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4554760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9175104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9175104 = ⟨1343350625, 1638117356⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4587552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9633808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9633808 = ⟨1657646420, 1401448297⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4816904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9830432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9830432 = ⟨569520201, 1315494327⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4915216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9961600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9961600 = ⟨158332735, 781423213⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4980800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10158096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10158096 = ⟨228825457, 1773949090⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5079048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10682384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10682384 = ⟨477624401, 421121034⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5341192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10879008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10879008 = ⟨1382045327, 1848075123⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5439504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11206672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11206672 = ⟨162657771, 1418419675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5603336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11272256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11272256 = ⟨1143904587, 540694832⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5636128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11534592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11534592 = ⟨1900601073, 1816344226⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5767296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11730960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11730960 = ⟨373731191, 505380245⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5865480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11927584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11927584 = ⟨1433184142, 1355414271⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5963792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12255248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12255248 = ⟨2054387424, 882277938⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6127624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12583936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12583936 = ⟨2123635407, 1081507110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6291968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12779536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12779536 = ⟨843944215, 1308987613⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6389768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12976160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12976160 = ⟨15093678, 1042445237⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6488080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13303824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13303824 = ⟨1755205335, 314595075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6651912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13369408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13369408 = ⟨1401739549, 1097491248⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6684704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13828112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13828112 = ⟨2086435924, 1226250586⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6914056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14024736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14024736 = ⟨513120300, 992027720⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7012368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14155904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14155904 = ⟨488715237, 940608935⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7077952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14352400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14352400 = ⟨1202375968, 870898318⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7176200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14876688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14876688 = ⟨832284506, 1680924300⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7438344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15073312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15073312 = ⟨412233176, 2032309657⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7536656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15400976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15400976 = ⟨1782637162, 315032635⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7700488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15466560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15466560 = ⟨570179120, 943054536⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7733280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15925264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15925264 = ⟨728826551, 149661993⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7962632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16121888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16121888 = ⟨1650357603, 7346171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8060944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16449552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16449552 = ⟨630694041, 1333208016⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8224776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17170464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17170464 = ⟨1618791272, 1362261400⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8585232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17563712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17563712 = ⟨1611470649, 1916772505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8781856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18219040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18219040 = ⟨1138903534, 2123529619⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9109520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18350208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18350208 = ⟨1009855734, 1023878457⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9175104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19267616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19267616 = ⟨1414381293, 812062823⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9633808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19660864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19660864 = ⟨1547714537, 2130940479⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9830432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19923200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19923200 = ⟨205358188, 1553245214⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9961600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20316192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20316192 = ⟨2057609289, 695557251⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10158096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21364768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21364768 = ⟨352316779, 1243403507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10682384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21758016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21758016 = ⟨856700564, 1457169910⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10879008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22413344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22413344 = ⟨64702323, 891825552⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11206672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22544512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22544512 = ⟨1579196318, 1348540420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11272256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23069184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23069184 = ⟨536044542, 1745864249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11534592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23461920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23461920 = ⟨1248901460, 1659932344⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11730960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23855168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23855168 = ⟨620395280, 780701337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11927584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24510496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24510496 = ⟨1932496262, 826060840⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12255248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25559072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25559072 = ⟨1403760855, 157239926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12779536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25952320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25952320 = ⟨183300436, 609917239⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12976160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26607648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26607648 = ⟨1583053042, 712174175⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13303824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26738816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26738816 = ⟨1757864877, 539478054⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13369408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27656224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27656224 = ⟨1663688332, 1315844960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13828112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28049472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28049472 = ⟨703998834, 1720432513⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14024736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28311808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28311808 = ⟨677395954, 1520471284⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14155904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28704800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28704800 = ⟨1979270898, 720825050⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14352400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29753376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29753376 = ⟨926476825, 401094955⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14876688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30146624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30146624 = ⟨781860034, 335143412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15073312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30801952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30801952 = ⟨988141455, 150230352⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15400976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30933120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30933120 = ⟨1296208970, 1941290138⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15466560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31850528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31850528 = ⟨1554473172, 298881725⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15925264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32243776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32243776 = ⟨71375739, 362693707⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16121888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32899104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32899104 = ⟨1016065997, 2000286676⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16449552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34340928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34340928 = ⟨1848871438, 1697161144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17170464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35127424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35127424 = ⟨1274142138, 171037034⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17563712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36438080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36438080 = ⟨723787116, 332150348⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18219040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36700416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36700416 = ⟨1421824733, 1874770121⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18350208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38535232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38535232 = ⟨1358545521, 752103212⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19267616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39321728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39321728 = ⟨2111962207, 353361234⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19660864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39846400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39846400 = ⟨38168553, 2125088080⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19923200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40632384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40632384 = ⟨382465072, 199024546⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20316192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42729536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42729536 = ⟨630622527, 584012157⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21364768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43516032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43516032 = ⟨1426286134, 853535083⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21758016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44826688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44826688 = ⟨161577297, 1660080726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22413344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45089024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45089024 = ⟨813379721, 988164410⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22544512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46138368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46138368 = ⟨242763393, 80138650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23069184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46923840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46923840 = ⟨1441430076, 1345847616⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23461920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47710336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47710336 = ⟨1110335683, 802146365⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23855168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49020992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49020992 = ⟨573623351, 1558322138⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24510496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51118144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51118144 = ⟨875022438, 1314261829⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25559072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51904640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51904640 = ⟨1318846400, 1066064178⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25952320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53215296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53215296 = ⟨1702674315, 521903989⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26607648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53477632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53477632 = ⟨1069110232, 841251345⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26738816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55312448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55312448 = ⟨1044634885, 401110988⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27656224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56098944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56098944 = ⟨812783631, 87864601⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28049472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56623616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56623616 = ⟨1651724207, 182674932⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28311808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57409600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57409600 = ⟨1850847193, 847903177⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28704800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59506752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59506752 = ⟨766079449, 1162779179⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29753376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60293248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60293248 = ⟨1637232914, 12620918⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30146624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61603904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61603904 = ⟨81974242, 1369523482⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30801952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61866240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61866240 = ⟨2103428316, 1983520630⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30933120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63701056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63701056 = ⟨949111615, 1407267626⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31850528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64487552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64487552 = ⟨521846748, 805524572⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32243776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65798208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65798208 = ⟨2023487912, 1606472278⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32899104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_68681856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 68681856 = ⟨1708098969, 1310925114⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34340928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_70254848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70254848 = ⟨1117505536, 1168259674⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35127424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72876160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72876160 = ⟨1083696905, 1397975187⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36438080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73400832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73400832 = ⟨23665417, 1435643760⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36700416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77070464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77070464 = ⟨1299652747, 656441737⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38535232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_78643456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 78643456 = ⟨858535500, 621874676⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39321728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_79692800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79692800 = ⟨1128749075, 1106851245⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39846400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_81264768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81264768 = ⟨1647694804, 71722872⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40632384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_85459072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 85459072 = ⟨1088711622, 1009754415⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42729536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87032064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87032064 = ⟨1158884981, 781046501⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43516032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89653376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89653376 = ⟨137517255, 1401827945⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44826688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90178048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90178048 = ⟨1047333005, 389051409⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45089024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_93847680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93847680 = ⟨57715678, 807525796⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46923840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_95420672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 95420672 = ⟨834499135, 1209383182⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47710336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98041984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98041984 = ⟨961766864, 1357535341⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49020992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102236288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102236288 = ⟨1650970535, 352937437⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51118144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_103809280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103809280 = ⟨1150147490, 898597351⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51904640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106430592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106430592 = ⟨954210985, 2090596689⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53215296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106955264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106955264 = ⟨1925087801, 1093934586⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53477632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_110624896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110624896 = ⟨1936918624, 1777693683⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55312448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_112197888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 112197888 = ⟨1139380541, 760006363⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56098944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_113247232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 113247232 = ⟨1870718732, 902417887⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56623616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_114819200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114819200 = ⟨912392351, 1975118736⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57409600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_119013504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119013504 = ⟨987405464, 1066669605⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59506752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120586496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120586496 = ⟨1909223356, 995602826⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60293248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123207808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123207808 = ⟨892085614, 1355432437⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61603904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123732480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123732480 = ⟨183362155, 826356275⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61866240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_127402112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 127402112 = ⟨636830999, 1121883084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63701056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_128975104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128975104 = ⟨806485802, 2141189189⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64487552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_131596416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131596416 = ⟨1830478039, 1322664901⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65798208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_137363712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 137363712 = ⟨1010977138, 1654442111⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68681856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_140509696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 140509696 = ⟨1574094766, 1419864749⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70254848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_145752320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 145752320 = ⟨2070917948, 337236609⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72876160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_146801664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 146801664 = ⟨75612694, 638305945⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73400832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_154140928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 154140928 = ⟨612211453, 610851573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77070464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_157286912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 157286912 = ⟨607314483, 1434872618⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78643456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_162529536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 162529536 = ⟨13849887, 1634375075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81264768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_170918144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 170918144 = ⟨233455892, 1126764267⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85459072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_174064128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 174064128 = ⟨1243997405, 2007624854⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87032064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_179306752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 179306752 = ⟨2048365357, 1970409609⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89653376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_180356096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 180356096 = ⟨1704605091, 1002003657⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90178048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_187695360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 187695360 = ⟨326369151, 49009497⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93847680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_190841344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 190841344 = ⟨715955897, 640913255⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_95420672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_196083968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 196083968 = ⟨1309969414, 264100485⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98041984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_204472576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 204472576 = ⟨1358008884, 1898762161⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102236288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_207618560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 207618560 = ⟨1127469614, 1538708570⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103809280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_212861184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 212861184 = ⟨1738065539, 1628467434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106430592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_213910528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 213910528 = ⟨1936509027, 329657887⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106955264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_221249792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 221249792 = ⟨1565424859, 214672772⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110624896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_224395776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 224395776 = ⟨183545232, 1553108188⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112197888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_229638400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 229638400 = ⟨1236188319, 993771895⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114819200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_238027008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 238027008 = ⟨460479247, 810730493⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119013504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_241172992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 241172992 = ⟨1126276025, 1714869064⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120586496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_246415616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 246415616 = ⟨180302585, 1178122616⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123207808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_247464960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 247464960 = ⟨1050410086, 1073301032⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123732480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_254804224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 254804224 = ⟨64623609, 63666264⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_127402112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_257950208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 257950208 = ⟨1743546773, 975402794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128975104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_263192832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 263192832 = ⟨1212777032, 1860738132⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131596416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_274727424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 274727424 = ⟨7404517, 72359405⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_137363712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_281019392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 281019392 = ⟨1274756874, 824918498⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_140509696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_291504640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 291504640 = ⟨354158595, 824035356⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_145752320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_308281856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 308281856 = ⟨1453129968, 1857289315⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_154140928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_314573824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 314573824 = ⟨202216255, 1166833230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_157286912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_325059072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 325059072 = ⟨1523707222, 186787952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_162529536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_341836288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 341836288 = ⟨624744187, 171168809⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_170918144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_348128256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 348128256 = ⟨1189119296, 1858928305⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_174064128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_358613504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 358613504 = ⟨1045386653, 901896387⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_179306752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_375390720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 375390720 = ⟨1343894514, 1306545781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_187695360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_381682688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 381682688 = ⟨1517692234, 1936279112⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_190841344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_392167936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 392167936 = ⟨172964911, 669263443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_196083968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_408945152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 408945152 = ⟨422457972, 1367307982⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_204472576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_415237120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 415237120 = ⟨1146595981, 37855626⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_207618560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_425722368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 425722368 = ⟨649001401, 1148957011⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_212861184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_442499584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 442499584 = ⟨1757037007, 64793988⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_221249792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_448791552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 448791552 = ⟨1228317011, 328390175⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_224395776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_459276800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 459276800 = ⟨386945248, 2018966406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_229638400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_476054016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 476054016 = ⟨1397006058, 18225283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_238027008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_482345984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 482345984 = ⟨2067891986, 853385273⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_241172992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_492831232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 492831232 = ⟨490104707, 1873170849⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_246415616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_509608448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 509608448 = ⟨931211608, 466068245⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_254804224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_515900416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 515900416 = ⟨558333589, 618725725⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_257950208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_526385664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 526385664 = ⟨1885348367, 113922615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_263192832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_549454848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 549454848 = ⟨1081507110, 23848240⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_274727424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_583009280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 583009280 = ⟨80138650, 1904720254⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_291504640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_616563712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 616563712 = ⟨1106851245, 1018734572⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_308281856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_650118144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 650118144 = ⟨902417887, 276764915⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_325059072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_683672576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 683672576 = ⟨638305945, 2071870953⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_341836288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_717227008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 717227008 = ⟨1002003657, 442878556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_358613504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_750781440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 750781440 = ⟨329657887, 210974620⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_375390720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_784335872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 784335872 = ⟨1073301032, 1097073561⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_392167936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_817890304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 817890304 = ⟨824918498, 872726773⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_408945152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_851444736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 851444736 = ⟨1166833230, 1945267392⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_425722368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_884999168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 884999168 = ⟨1858928305, 958364351⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_442499584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_918553600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 918553600 = ⟨1936279112, 629791413⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_459276800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_952108032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 952108032 = ⟨37855626, 1000887666⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_476054016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_985662464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 985662464 = ⟨328390175, 919166636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_492831232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1019216896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1019216896 = ⟨853385273, 79591661⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_509608448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1052771328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1052771328 = ⟨618725725, 1589150058⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_526385664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 192) = ⟨2123635407, 1081507110⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 192 = 12583936 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_12583936

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2123635407, 1081507110⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 192) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 193) = ⟨1081507110, 23848240⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 193 = 549454848 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_549454848

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1081507110, 23848240⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 193) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 194) = ⟨1274756874, 824918498⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 194 = 281019392 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_281019392

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1274756874, 824918498⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 194) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 195) = ⟨824918498, 872726773⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 195 = 817890304 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_817890304

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨824918498, 872726773⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 195) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 196) = ⟨75612694, 638305945⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 196 = 146801664 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_146801664

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨75612694, 638305945⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 196) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 197) = ⟨638305945, 2071870953⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 197 = 683672576 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_683672576

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨638305945, 2071870953⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 197) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 198) = ⟨1146595981, 37855626⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 198 = 415237120 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_415237120

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1146595981, 37855626⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 198) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 199) = ⟨37855626, 1000887666⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 199 = 952108032 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_952108032

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨37855626, 1000887666⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 199) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 200) = ⟨1128749075, 1106851245⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 200 = 79692800 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_79692800

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1128749075, 1106851245⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 200) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 201) = ⟨1106851245, 1018734572⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 201 = 616563712 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_616563712

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1106851245, 1018734572⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 201) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 202) = ⟨1189119296, 1858928305⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 202 = 348128256 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_348128256

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1189119296, 1858928305⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 202) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 203) = ⟨1858928305, 958364351⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 203 = 884999168 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_884999168

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1858928305, 958364351⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 203) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 204) = ⟨1936509027, 329657887⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 204 = 213910528 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_213910528

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1936509027, 329657887⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 204) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 205) = ⟨329657887, 210974620⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 205 = 750781440 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_750781440

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨329657887, 210974620⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 205) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 206) = ⟨2067891986, 853385273⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 206 = 482345984 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_482345984

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2067891986, 853385273⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 206) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 207) = ⟨853385273, 79591661⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 207 = 1019216896 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1019216896

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨853385273, 79591661⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 207) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 208) = ⟨242763393, 80138650⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 208 = 46138368 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_46138368

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨242763393, 80138650⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 208) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 209) = ⟨80138650, 1904720254⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 209 = 583009280 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_583009280

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨80138650, 1904720254⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 209) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 210) = ⟨202216255, 1166833230⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 210 = 314573824 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_314573824

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨202216255, 1166833230⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 210) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 211) = ⟨1166833230, 1945267392⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 211 = 851444736 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_851444736

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1166833230, 1945267392⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 211) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 212) = ⟨1704605091, 1002003657⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 212 = 180356096 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_180356096

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1704605091, 1002003657⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 212) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 213) = ⟨1002003657, 442878556⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 213 = 717227008 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_717227008

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1002003657, 442878556⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 213) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 214) = ⟨1228317011, 328390175⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 214 = 448791552 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_448791552

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1228317011, 328390175⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 214) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 215) = ⟨328390175, 919166636⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 215 = 985662464 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_985662464

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨328390175, 919166636⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 215) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 216) = ⟨1870718732, 902417887⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 216 = 113247232 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_113247232

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1870718732, 902417887⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 216) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 217) = ⟨902417887, 276764915⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 217 = 650118144 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_650118144

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨902417887, 276764915⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 217) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 218) = ⟨1517692234, 1936279112⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 218 = 381682688 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_381682688

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1517692234, 1936279112⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 218) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 219) = ⟨1936279112, 629791413⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 219 = 918553600 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_918553600

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1936279112, 629791413⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 219) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 220) = ⟨1050410086, 1073301032⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 220 = 247464960 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_247464960

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1050410086, 1073301032⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 220) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 221) = ⟨1073301032, 1097073561⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 221 = 784335872 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_784335872

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1073301032, 1097073561⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 221) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 222) = ⟨558333589, 618725725⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 222 = 515900416 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_515900416

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨558333589, 618725725⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 222) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 223) = ⟨618725725, 1589150058⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 223 = 1052771328 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1052771328

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨618725725, 1589150058⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 223) := by
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

end R17TableAChunk06Certificate
