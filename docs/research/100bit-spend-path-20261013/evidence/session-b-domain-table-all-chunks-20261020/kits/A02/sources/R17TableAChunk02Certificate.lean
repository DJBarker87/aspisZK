import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk02Certificate
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

theorem power_64 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64 = ⟨2042371533, 1362265296⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65 = ⟨1106294891, 184370010⟩ := by
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

theorem power_69 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69 = ⟨878709433, 901181160⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34]
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

theorem power_77 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77 = ⟨1255986648, 1483159588⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_80 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 80 = ⟨251214192, 1557021428⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_81 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81 = ⟨1283630603, 1419035398⟩ := by
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

theorem power_85 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 85 = ⟨807730929, 1079284455⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42]
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

theorem power_101 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101 = ⟨1779769850, 1133066291⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104 = ⟨595835346, 937999867⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52]
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

theorem power_117 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117 = ⟨1804617719, 1766370095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58]
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

theorem power_125 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125 = ⟨228087554, 1931649501⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128 = ⟨212706801, 1223819887⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_130 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 130 = ⟨182745460, 1218067210⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65]
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

theorem power_138 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 138 = ⟨289576174, 117745875⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69]
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

theorem power_154 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 154 = ⟨324269316, 652412893⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 160 = ⟨352777635, 313115116⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_162 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 162 = ⟨154394112, 954850232⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81]
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

theorem power_170 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 170 = ⟨1200476557, 337352944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85]
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

theorem power_186 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 186 = ⟨522032805, 1817076066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_194 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 194 = ⟨1182794174, 308889576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_97]
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

theorem power_202 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 202 = ⟨1860360142, 751729554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 208 = ⟨1397719779, 1280626794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104]
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

theorem power_218 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 218 = ⟨720704015, 1704001039⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_226 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 226 = ⟨907508540, 886854930⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_113]
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

theorem power_234 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 234 = ⟨1023252104, 151076554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117]
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

theorem power_250 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 250 = ⟨1254622717, 393467164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 256 = ⟨421007138, 256177860⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_260 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 260 = ⟨1113083573, 364920195⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_130]
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

theorem power_276 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 276 = ⟨2136981225, 76442191⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_138]
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

theorem power_296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 296 = ⟨224965265, 159335170⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_148]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_308 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 308 = ⟨1275566012, 926001803⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_154]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 320 = ⟨1637047685, 109864373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_324 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 324 = ⟨1784332407, 479339180⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_162]
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

theorem power_340 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 340 = ⟨1035137668, 1694074029⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_170]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_356 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 356 = ⟨115833841, 1001104970⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_178]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 360 = ⟨1022383927, 1626835633⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_180]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_372 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 372 = ⟨1865434190, 2013555186⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_186]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_388 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 388 = ⟨430904798, 52332054⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_194]
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

theorem power_404 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 404 = ⟨1264991587, 1665650581⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_202]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 416 = ⟨1719486678, 1121851154⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_420 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 420 = ⟨762451310, 2110959177⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_210]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 424 = ⟨167179466, 382336254⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_212]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_436 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 436 = ⟨416123875, 1134162993⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_218]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_452 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 452 = ⟨233641138, 250640687⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_226]
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

theorem power_468 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 468 = ⟨2093397897, 1522550679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_234]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_484 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 484 = ⟨1722484487, 1875389337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_242]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 488 = ⟨1001236781, 1044516446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_244]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_500 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 500 = ⟨373864208, 678267884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_250]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 512 = ⟨6346213, 905523693⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 520 = ⟨1443640351, 1408176577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_260]
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

theorem power_552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 552 = ⟨1478094092, 46019520⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_276]
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

theorem power_592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 592 = ⟨462102546, 1660293932⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 616 = ⟨1723903332, 1162738935⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_308]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 640 = ⟨982766847, 1369509443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 648 = ⟨293244124, 1145620673⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_324]
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

theorem power_680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 680 = ⟨1444330179, 873729398⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_340]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 712 = ⟨1788714561, 1660296709⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_356]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 720 = ⟨330499511, 1255545984⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 744 = ⟨1746837725, 1648052895⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_372]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 776 = ⟨286458136, 172269328⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_388]
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

theorem power_808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 808 = ⟨1343024069, 808079406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_404]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 832 = ⟨529167155, 49384636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 840 = ⟨667660294, 1845636271⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_420]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 848 = ⟨639667341, 414959610⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 872 = ⟨1436111776, 1927355740⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_436]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 904 = ⟨1367889452, 60689743⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_452]
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

theorem power_936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 936 = ⟨977714903, 1051251569⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_468]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 968 = ⟨331985874, 1829534965⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_484]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 976 = ⟨1625484020, 323681644⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1000 = ⟨2140279415, 2123398265⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_500]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1024 = ⟨1022251061, 788094511⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1040 = ⟨1991902696, 973993416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_520]
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

theorem power_1104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1104 = ⟨1224066945, 216858013⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_552]
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

theorem power_1184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1184 = ⟨1392219141, 868524623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1232 = ⟨467208929, 1117284316⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1280 = ⟨1774187400, 1713497086⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1296 = ⟨321437598, 88488468⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_648]
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

theorem power_1360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1360 = ⟨1062534928, 1483827896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1424 = ⟨1421359463, 688309433⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1440 = ⟨1445302729, 1296213244⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1488 = ⟨2066061064, 79229564⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1552 = ⟨934314680, 892942796⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_776]
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

theorem power_1616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1616 = ⟨190241594, 1357019236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1664 = ⟨288424812, 1959942454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1680 = ⟨97994513, 427567333⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1696 = ⟨797688518, 1724894293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1744 = ⟨329186677, 1544326724⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1808 = ⟨1868655533, 366044347⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_904]
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

theorem power_1872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1872 = ⟨1690319162, 1749624555⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1936 = ⟨440725243, 397214378⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1952 = ⟨1871828618, 1847683492⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2000 = ⟨1147858255, 2118048⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2048 = ⟨1633461177, 574296567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2080 = ⟨1187370746, 926533015⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1040]
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

theorem power_2208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2208 = ⟨1676955329, 1180692240⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1104]
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

theorem power_2368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2368 = ⟨39852141, 123936243⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2464 = ⟨1542370492, 267773083⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2560 = ⟨1743980363, 345791924⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2592 = ⟨1331074750, 1831714204⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1296]
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

theorem power_2720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2720 = ⟨1072531720, 1896677731⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2848 = ⟨1107539930, 1867229522⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2880 = ⟨2050207099, 979596272⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2976 = ⟨1338602267, 1116448727⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3104 = ⟨1341394939, 1875262719⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1552]
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

theorem power_3232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3232 = ⟨124445571, 706631523⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3328 = ⟨1399167609, 1906303117⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3360 = ⟨957961597, 1713758465⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3392 = ⟨968612238, 1641022910⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3488 = ⟨1891426405, 1154799597⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3616 = ⟨1520347037, 753194884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1808]
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

theorem power_3744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3744 = ⟨103855733, 1898302976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3872 = ⟨732405916, 440343212⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3904 = ⟨314388810, 1013513450⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4000 = ⟨2079500206, 62336377⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4096 = ⟨595037635, 2111542451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4160 = ⟨1624834588, 1587955294⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2080]
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

theorem power_4416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4416 = ⟨408933184, 381501510⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2208]
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

theorem power_4736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4736 = ⟨272617121, 579551580⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4928 = ⟨1851793512, 331539505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5120 = ⟨235158087, 2112924242⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5184 = ⟨724607827, 1581281339⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2592]
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

theorem power_5440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5440 = ⟨607008739, 948334533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5696 = ⟨979531440, 1806178696⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5760 = ⟨175645010, 1734378279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5952 = ⟨533092340, 383019730⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6208 = ⟨651225695, 496791815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3104]
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

theorem power_6464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6464 = ⟨976698970, 920955611⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6656 = ⟨1510720600, 1956487951⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6720 = ⟨618506335, 666669213⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6784 = ⟨1220597866, 72538165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6976 = ⟨950603389, 1193852273⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7232 = ⟨1868836168, 945793409⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3616]
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

theorem power_7488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7488 = ⟨1416522298, 2020079164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7744 = ⟨1314764028, 76457491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7808 = ⟨1996451271, 146269947⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8000 = ⟨1034240275, 1347145792⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8193 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8193 = ⟨995436393, 1641048635⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8320 = ⟨965135430, 672085251⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4160]
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

theorem power_8832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8832 = ⟨2028834280, 858819348⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4416]
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

theorem power_9472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9472 = ⟨2016094574, 1147504298⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9856 = ⟨579818567, 708464220⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10240 = ⟨1242192167, 1322293366⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10368 = ⟨801839679, 1416549508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5184]
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

theorem power_10880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10880 = ⟨134399697, 892423737⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11392 = ⟨1624277146, 218264369⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11520 = ⟨1411573869, 756888130⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11904 = ⟨387321092, 162791576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12416 = ⟨1634623176, 1242708781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6208]
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

theorem power_12928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12928 = ⟨2024521721, 865260240⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13312 = ⟨721344225, 1097609337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13440 = ⟨1254228892, 1773606283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13568 = ⟨1050297291, 98481735⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13952 = ⟨1440836092, 1085471181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14464 = ⟨1919214175, 72145384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7232]
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

theorem power_14976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14976 = ⟨2067447709, 1097691368⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15488 = ⟨2114691705, 1438921723⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15616 = ⟨139198880, 1155184073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16000 = ⟨1030880657, 718864663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16386 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16386 = ⟨1721222167, 1429300573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8193]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16640 = ⟨71597582, 502509710⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8320]
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

theorem power_17664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17664 = ⟨15796839, 1693524553⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8832]
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

theorem power_18944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18944 = ⟨83021569, 1776986900⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19712 = ⟨1355473385, 1096376971⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20480 = ⟨433600440, 167145119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20736 = ⟨753306136, 1377615667⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10368]
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

theorem power_21760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21760 = ⟨207134484, 1863212449⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22784 = ⟨136897115, 493987288⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23040 = ⟨512700922, 986405252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23808 = ⟨1929818386, 55540944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24832 = ⟨1648510500, 90235145⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12416]
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

theorem power_25856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25856 = ⟨1354554672, 1833839332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26624 = ⟨2056541252, 1900478857⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26880 = ⟨676135582, 533441857⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27136 = ⟨698096929, 432547149⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27904 = ⟨351222675, 1148291511⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28928 = ⟨1228915707, 1186399647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14464]
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

theorem power_29952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29952 = ⟨1852134147, 634458272⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30976 = ⟨1799654460, 431926545⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31232 = ⟨1863885482, 1326705008⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32000 = ⟨424799909, 191617025⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32772 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32772 = ⟨522165519, 710761940⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16386]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33280 = ⟨1263299221, 1709334650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16640]
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

theorem power_35328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35328 = ⟨750253747, 530937643⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17664]
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

theorem power_37888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37888 = ⟨451882769, 1853894340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39424 = ⟨1008501773, 1237883647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40961 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40961 = ⟨1635016903, 1186551077⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41472 = ⟨2059141329, 885416319⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20736]
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

theorem power_43520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43520 = ⟨1133865341, 1051269249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45568 = ⟨1781787493, 1860062069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46080 = ⟨2092093316, 989477899⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47616 = ⟨895473556, 561535522⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49664 = ⟨845849999, 1932927210⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24832]
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

theorem power_51712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51712 = ⟨554838094, 2082603647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53248 = ⟨528497962, 2048433423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53760 = ⟨2139509494, 188640990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54272 = ⟨1176403617, 782773078⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55808 = ⟨193409102, 1106498791⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57856 = ⟨922379982, 1084651240⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28928]
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

theorem power_59904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59904 = ⟨486461911, 1395218254⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61952 = ⟨489478772, 1893340241⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62464 = ⟨1733341057, 673759763⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64000 = ⟨1137104901, 634195134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65544 = ⟨656244101, 569978235⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32772]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66560 = ⟨1581705852, 1303922066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33280]
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

theorem power_70656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70656 = ⟨1921779281, 131885⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73729 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73729 = ⟨1132840246, 1737038237⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_74752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 74752 = ⟨650673267, 783237242⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_75776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 75776 = ⟨1210077794, 246102266⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_78848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 78848 = ⟨912283038, 323725110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_81922 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81922 = ⟨1648447068, 322412399⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40961]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_82944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 82944 = ⟨961560740, 1336435363⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41472]
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

theorem power_87040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87040 = ⟨290570175, 898698902⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_91136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 91136 = ⟨1033720207, 1183348280⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92160 = ⟨713314261, 425545952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_95232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 95232 = ⟨658974643, 1874009431⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_99328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 99328 = ⟨1790091302, 24162003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49664]
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

theorem power_103424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103424 = ⟨733457982, 495056491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106497 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106497 = ⟨1236021166, 1679284065⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_107520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 107520 = ⟨250559477, 97699828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108544 = ⟨1032881673, 494228663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_111616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 111616 = ⟨1624655281, 300914040⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115712 = ⟨1719401654, 122790862⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57856]
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

theorem power_119808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119808 = ⟨1114403665, 611529715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123904 = ⟨1105219207, 965100990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124928 = ⟨346773666, 152947344⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_128000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128000 = ⟨1070571079, 1366506169⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_131088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131088 = ⟨2135051457, 2146754318⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_133120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 133120 = ⟨1343125376, 1611076075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_135168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 135168 = ⟨798338207, 2110850421⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_139265 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 139265 = ⟨57325222, 826491712⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_141312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 141312 = ⟨1719915550, 648525961⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_147458 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 147458 = ⟨1397586762, 1738563327⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73729]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_149504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 149504 = ⟨1071628068, 1255434837⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_151552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 151552 = ⟨2001642678, 1520422911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_157696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 157696 = ⟨611826819, 1330717448⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_163844 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 163844 = ⟨1010869437, 1157694447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81922]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_165888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 165888 = ⟨821570021, 1145420705⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_167936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 167936 = ⟨729011542, 952009042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_172033 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 172033 = ⟨867881794, 438694841⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_174080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 174080 = ⟨229177162, 396528583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_182272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 182272 = ⟨1309999598, 467334114⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_184320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 184320 = ⟨1029245122, 1158447597⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_190464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 190464 = ⟨1124013519, 1413144457⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_95232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_198656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 198656 = ⟨1408282706, 600722738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_200704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 200704 = ⟨1631496031, 481893475⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_204801 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 204801 = ⟨16256508, 582231299⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_206848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 206848 = ⟨1817546580, 1225707862⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_212994 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 212994 = ⟨36786317, 17752620⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106497]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_215040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 215040 = ⟨511564144, 1485902172⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_107520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_217088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 217088 = ⟨1876139646, 119923533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_223232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 223232 = ⟨1078945591, 1940049095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_231424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 231424 = ⟨1423034495, 1044300741⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_233472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 233472 = ⟨953139263, 265503960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_237569 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 237569 = ⟨2032786917, 1521354719⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_239616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 239616 = ⟨1300505822, 1483719533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_247808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 247808 = ⟨1752942601, 1104368066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_249856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 249856 = ⟨887385898, 608769478⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_256000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 256000 = ⟨1425723522, 1087018637⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_262176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 262176 = ⟨1310308431, 961485752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_266240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 266240 = ⟨2008329732, 1737289791⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_270337 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 270337 = ⟨1852096814, 399510042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_135168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_278530 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 278530 = ⟨1337956949, 981172773⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_139265]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_282624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 282624 = ⟨18918067, 521344418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_141312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_294916 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 294916 = ⟨808826973, 172451122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_147458]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_299008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 299008 = ⟨1318914216, 1663922738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_149504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_303105 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 303105 = ⟨469616235, 288300269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_151552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_315392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 315392 = ⟨1576856103, 1461690978⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_157696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_327688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 327688 = ⟨2042551614, 1895869752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_163844]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_331776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 331776 = ⟨1250840269, 386418603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_165888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_335873 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 335873 = ⟨1940735373, 1548291021⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_167936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_344066 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 344066 = ⟨374053911, 2135634999⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_172033]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_348160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 348160 = ⟨183117139, 65944434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_174080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_364544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 364544 = ⟨291679777, 1578449442⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_182272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_368641 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 368641 = ⟨1857906205, 726144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_184320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_380928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 380928 = ⟨647843950, 788293466⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_190464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_397312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 397312 = ⟨1819903752, 1929668715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_198656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_401409 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 401409 = ⟨992983925, 865265653⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_200704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_409602 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 409602 = ⟨839573899, 1421979020⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_204801]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_413696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 413696 = ⟨1936661821, 241049853⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_206848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_425988 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 425988 = ⟨1186469465, 1017244739⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_212994]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_430080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 430080 = ⟨782570832, 476532960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_215040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_434177 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 434177 = ⟨1676920652, 902759576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_217088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_446464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 446464 = ⟨2076036242, 130048956⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_223232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_462848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 462848 = ⟨422755315, 374503008⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_231424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_466945 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 466945 = ⟨1204606777, 2074880702⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_233472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_475138 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 475138 = ⟨12634144, 873165755⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_237569]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_479232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 479232 = ⟨174156438, 1448257952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_239616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_495616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 495616 = ⟨1954241062, 1820169310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_247808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_499713 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 499713 = ⟨800536327, 555639095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_249856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_512000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 512000 = ⟨1615674956, 1808914239⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_256000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_524352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 524352 = ⟨797838424, 1720388937⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_262176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_532481 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 532481 = ⟨134774385, 2037503679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_266240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_540674 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 540674 = ⟨1238875956, 593617829⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_270337]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_557060 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 557060 = ⟨522191634, 1085176535⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_278530]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_565249 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 565249 = ⟨786112601, 1093076661⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_282624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_589832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 589832 = ⟨450913588, 1204392693⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_294916]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_598017 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 598017 = ⟨2104867724, 2058352378⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_299008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_606210 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 606210 = ⟨1120759586, 1880542678⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_303105]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_630785 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 630785 = ⟨781423078, 10442848⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_315392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_655376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 655376 = ⟨1846551503, 1300029253⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_327688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_663553 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 663553 = ⟨18370524, 240395068⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_331776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_671746 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 671746 = ⟨1409492577, 1353882821⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_335873]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_688132 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 688132 = ⟨420505796, 1069065835⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_344066]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_696321 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 696321 = ⟨521238400, 42230713⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_348160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_729089 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 729089 = ⟨1419004746, 523816937⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_364544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_737282 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 737282 = ⟨1991736853, 468439302⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_368641]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_761857 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 761857 = ⟨1057280692, 1188800764⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_380928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_794625 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 794625 = ⟨915151132, 1868601880⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_397312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_802818 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 802818 = ⟨1328573482, 214948026⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_401409]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_819204 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 819204 = ⟨172246324, 2123908753⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_409602]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_827393 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 827393 = ⟨1348256119, 877844780⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_413696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_851976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 851976 = ⟨1777047620, 75582387⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_425988]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_860161 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 860161 = ⟨567272634, 2039385659⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_430080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_868354 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 868354 = ⟨385371715, 1755855600⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_434177]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_892929 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 892929 = ⟨1647975883, 1591026790⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_446464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_925697 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 925697 = ⟨741444350, 1978662725⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_462848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_933890 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 933890 = ⟨2082382470, 1342505140⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_466945]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_950276 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 950276 = ⟨417746098, 13493209⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_475138]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_958465 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 958465 = ⟨1023558421, 477486653⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_479232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_991233 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 991233 = ⟨411157577, 63110960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_495616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_999426 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 999426 = ⟨926886322, 616698302⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_499713]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1024001 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1024001 = ⟨795197959, 1187926800⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_512000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1048704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1048704 = ⟨667326951, 1610985534⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_524352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1064962 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1064962 = ⟨1812528253, 823259551⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_532481]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1081348 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1081348 = ⟨360728729, 325951294⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_540674]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1114120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1114120 = ⟨1345711491, 379530772⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_557060]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1130498 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1130498 = ⟨1392945826, 1144064293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_565249]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1179664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1179664 = ⟨827165214, 1186896962⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_589832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1196034 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1196034 = ⟨1420584527, 407682312⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_598017]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1212420 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1212420 = ⟨790579626, 38375628⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_606210]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1261570 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1261570 = ⟨880421701, 522421103⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_630785]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1310752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1310752 = ⟨51118572, 786438632⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_655376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1327106 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1327106 = ⟨341300698, 567957787⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_663553]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1343492 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1343492 = ⟨374744680, 208777169⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_671746]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1376264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1376264 = ⟨546341421, 1716140882⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_688132]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1392642 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1392642 = ⟨1017475207, 652511019⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_696321]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1458178 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1458178 = ⟨1462730758, 1297457585⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_729089]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1474564 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1474564 = ⟨343149174, 1221659050⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_737282]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1523714 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1523714 = ⟨1948589134, 466133947⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_761857]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1589250 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1589250 = ⟨1084920620, 1147647560⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_794625]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1605636 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1605636 = ⟨887266674, 883576343⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_802818]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1638408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1638408 = ⟨1313850258, 1765649052⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_819204]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1654786 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1654786 = ⟨1684124857, 1775084450⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_827393]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1703952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1703952 = ⟨236851971, 1185643715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_851976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1720322 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1720322 = ⟨1546433909, 170009236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_860161]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1736708 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1736708 = ⟨62407742, 1653144001⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_868354]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1785858 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1785858 = ⟨1974038005, 1477137103⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_892929]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1851394 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1851394 = ⟨1072295294, 156187725⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_925697]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1867780 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1867780 = ⟨232947898, 1065388890⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_933890]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1900552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1900552 = ⟨391400900, 2010500118⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_950276]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1916930 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1916930 = ⟨2046316389, 62897496⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_958465]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1982466 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1982466 = ⟨965088245, 1808255397⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_991233]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1998852 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1998852 = ⟨1081986439, 1187944051⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_999426]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2048002 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2048002 = ⟨541282086, 876405796⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1024001]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2097408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2097408 = ⟨946622652, 1451465675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1048704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2129924 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2129924 = ⟨671809403, 1409034455⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1064962]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2162696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2162696 = ⟨375785384, 1394745764⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1081348]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2228240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2228240 = ⟨230334794, 316422615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1114120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2260996 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2260996 = ⟨1717332045, 845637912⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1130498]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2359328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2359328 = ⟨1595658358, 257387803⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1179664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2392068 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2392068 = ⟨1713141175, 149239839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1196034]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2424840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2424840 = ⟨1399770436, 2036321161⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1212420]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2523140 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2523140 = ⟨1160769718, 782266208⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1261570]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2621504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2621504 = ⟨1819051405, 224321636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1310752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2654212 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2654212 = ⟨1075337595, 1396924867⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1327106]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2686984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2686984 = ⟨1863434973, 1834269307⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1343492]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2752528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2752528 = ⟨2050310216, 1252276113⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1376264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2785284 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2785284 = ⟨1215343879, 93648801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1392642]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2916356 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2916356 = ⟨590956441, 1477206446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1458178]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2949128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2949128 = ⟨1564751286, 1590397573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1474564]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3047428 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3047428 = ⟨371256232, 1351512831⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1523714]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3178500 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3178500 = ⟨1466829846, 2075877329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1589250]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3211272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3211272 = ⟨133001162, 798399714⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1605636]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3276816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3276816 = ⟨1658474148, 1498321813⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1638408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3309572 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3309572 = ⟨352273742, 1342776898⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1654786]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3407904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3407904 = ⟨391649924, 1037342525⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1703952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3440644 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3440644 = ⟨1986918365, 1502677295⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1720322]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3473416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3473416 = ⟨1054430965, 271687696⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1736708]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3571716 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3571716 = ⟨1975145347, 1465683652⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1785858]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3702788 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3702788 = ⟨523302560, 320599083⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1851394]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3735560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3735560 = ⟨1565013040, 248731836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1867780]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3801104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3801104 = ⟨956302096, 709127488⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1900552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3833860 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3833860 = ⟨890350416, 1573700878⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1916930]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3964932 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3964932 = ⟨868777313, 1743925075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1982466]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3997704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3997704 = ⟨1990954168, 1048486046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1998852]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4096004 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4096004 = ⟨486312247, 470766875⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2048002]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4194816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4194816 = ⟨569006265, 1647920563⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2097408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4259848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4259848 = ⟨1647463278, 587438281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2129924]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4325392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4325392 = ⟨2081162346, 376136488⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2162696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4456480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4456480 = ⟨356402312, 1317640603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2228240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4521992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4521992 = ⟨526671924, 1366707898⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2260996]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4718656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4718656 = ⟨2057210812, 1516430770⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2359328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4784136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4784136 = ⟨926700929, 1174132840⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2392068]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4849680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4849680 = ⟨852498524, 1154738348⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2424840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5046280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5046280 = ⟨220136889, 1956266435⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2523140]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5243008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5243008 = ⟨284596754, 447864018⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2621504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5308424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5308424 = ⟨215891563, 78419668⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2654212]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5373968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5373968 = ⟨2015168110, 1526705968⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2686984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5505056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5505056 = ⟨88300002, 1555621491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2752528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5570568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5570568 = ⟨1747138576, 1745260331⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2785284]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5832712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5832712 = ⟨733170804, 1626134766⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2916356]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5898256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5898256 = ⟨668221331, 1402000439⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2949128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6094856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6094856 = ⟨1300393841, 1907458063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3047428]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6357000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6357000 = ⟨644092381, 1674807191⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3178500]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6422544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6422544 = ⟨1923414043, 303339181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3211272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6553632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6553632 = ⟨1201679262, 1179702856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3276816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6619144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6619144 = ⟨791792900, 1441856332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3309572]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6815808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6815808 = ⟨1937896566, 2020728623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3407904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6881288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6881288 = ⟨1468180613, 1340464122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3440644]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6946832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6946832 = ⟨662636414, 26095603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3473416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7143432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7143432 = ⟨1069795807, 718323861⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3571716]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7405576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7405576 = ⟨1650678879, 530842271⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3702788]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7471120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7471120 = ⟨322779937, 44662092⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3735560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7602208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7602208 = ⟨1926678387, 146938707⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3801104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7667720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7667720 = ⟨1384725148, 1960793448⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3833860]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7929864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7929864 = ⟨1070971236, 529107219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3964932]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7995408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7995408 = ⟨845015868, 78163714⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3997704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8192008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8192008 = ⟨2026418218, 2039145821⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4096004]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8389632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8389632 = ⟨400584953, 469433912⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4194816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8519696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8519696 = ⟨554530063, 2061113539⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4259848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8650784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8650784 = ⟨611683109, 591110892⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4325392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8912960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8912960 = ⟨796797453, 2062752892⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4456480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9043984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9043984 = ⟨1492381630, 140545281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4521992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9437312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9437312 = ⟨1536778656, 60102860⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4718656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9568272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9568272 = ⟨1840890327, 581668964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4784136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9699360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9699360 = ⟨939166925, 840225869⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4849680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10092560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10092560 = ⟨1552820413, 1621525590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5046280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10486016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10486016 = ⟨1931630017, 1767573672⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5243008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10616848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10616848 = ⟨875453594, 2046123193⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5308424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10747936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10747936 = ⟨194483151, 194607803⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5373968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11010112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11010112 = ⟨2401267, 1820647126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5505056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11141136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11141136 = ⟨1791003541, 511351997⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5570568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11665424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11665424 = ⟨267456043, 175412136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5832712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11796512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11796512 = ⟨1665976881, 836775229⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5898256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12189712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12189712 = ⟨275596735, 1789744085⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6094856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12714000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12714000 = ⟨987079487, 1897125784⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6357000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12845088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12845088 = ⟨192283342, 1985101755⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6422544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13107264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13107264 = ⟨839244968, 209082524⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6553632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13238288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13238288 = ⟨1379671037, 2088200889⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6619144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13631616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13631616 = ⟨1764907825, 455771636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6815808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13762576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13762576 = ⟨1873669913, 2025211412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6881288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13893664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13893664 = ⟨1054347594, 1822832833⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6946832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14286864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14286864 = ⟨358329573, 1237317184⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7143432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14811152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14811152 = ⟨886946727, 1362787684⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7405576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14942240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14942240 = ⟨1217202737, 1316500171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7471120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15204416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15204416 = ⟨1163915940, 1331346324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7602208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15335440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15335440 = ⟨1530325646, 1122760008⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7667720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15859728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15859728 = ⟨1023339732, 2124628189⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7929864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15990816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15990816 = ⟨186758528, 1400787943⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7995408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16384016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16384016 = ⟨430348213, 1403302190⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8192008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17039392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17039392 = ⟨2133545292, 1232170655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8519696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17301568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17301568 = ⟨1537964828, 1374921084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8650784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17825920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17825920 = ⟨111595466, 794197228⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8912960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18087968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18087968 = ⟨1108547350, 572775254⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9043984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18874624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18874624 = ⟨806282550, 673328168⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9437312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19136544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19136544 = ⟨1596365965, 2145133265⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9568272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19398720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19398720 = ⟨2023763758, 1707225423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9699360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20185120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20185120 = ⟨640231414, 1785222195⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10092560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20972032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20972032 = ⟨1662709147, 1227535974⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10486016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21233696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21233696 = ⟨473534807, 1942239931⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10616848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21495872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21495872 = ⟨2100053134, 1641748073⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10747936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22020224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22020224 = ⟨179226187, 1685171967⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11010112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22282272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22282272 = ⟨1363565334, 1933998058⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11141136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23330848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23330848 = ⟨1937113347, 2017111639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11665424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23593024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23593024 = ⟨1067755628, 919614236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11796512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24379424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24379424 = ⟨864314994, 1016554047⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12189712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25428000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25428000 = ⟨1811190791, 1999838889⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12714000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25690176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25690176 = ⟨367863320, 485608637⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12845088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26214528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26214528 = ⟨547063247, 863372848⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13107264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26476576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26476576 = ⟨1425600574, 1597103818⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13238288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27263232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27263232 = ⟨271131034, 1232724762⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13631616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27525152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27525152 = ⟨756322037, 1277114657⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13762576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27787328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27787328 = ⟨1238060475, 268584681⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13893664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28573728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28573728 = ⟨1782953592, 242298747⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14286864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29622304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29622304 = ⟨1802641158, 1329635965⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14811152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29884480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29884480 = ⟨1728202880, 1787655209⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14942240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30408832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30408832 = ⟨311977257, 213970789⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15204416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30670880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30670880 = ⟨2141202346, 602712317⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15335440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31719456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31719456 = ⟨431035032, 87580511⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15859728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31981632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31981632 = ⟨424421412, 722222423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15990816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32768032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32768032 = ⟨1871569946, 1964301746⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16384016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34078784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34078784 = ⟨526542104, 1622350189⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17039392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34603136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34603136 = ⟨948258734, 1669495124⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17301568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35651840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35651840 = ⟨905023621, 696142379⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17825920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36175936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36175936 = ⟨1391022358, 1503023086⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18087968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37749248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37749248 = ⟨1650043407, 65874228⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18874624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38273088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38273088 = ⟨212271968, 1427175776⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19136544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38797440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38797440 = ⟨666770017, 1383040856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19398720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40370240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40370240 = ⟨1288878770, 636599113⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20185120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41944064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41944064 = ⟨494932510, 292984488⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20972032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42467392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42467392 = ⟨854977045, 1010547830⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21233696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42991744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42991744 = ⟨321423346, 1886403507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21495872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44040448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44040448 = ⟨148942641, 347540747⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22020224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44564544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44564544 = ⟨538423215, 599318816⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22282272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46661696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46661696 = ⟨299301193, 30925672⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23330848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47186048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47186048 = ⟨27635285, 2099369905⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23593024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48758848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48758848 = ⟨513157812, 886812574⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24379424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50856000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50856000 = ⟨1878631939, 561517338⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25428000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51380352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51380352 = ⟨62477373, 1476073282⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25690176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52429056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52429056 = ⟨768768637, 1940124198⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26214528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52953152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52953152 = ⟨66706676, 1403413720⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26476576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54526464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54526464 = ⟨328125571, 1679007927⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27263232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55050304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55050304 = ⟨804936852, 334126368⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27525152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55574656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55574656 = ⟨1567513685, 737621490⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27787328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57147456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57147456 = ⟨771025117, 99129640⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28573728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59244608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59244608 = ⟨110578563, 415450386⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29622304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59768960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59768960 = ⟨316397937, 418295059⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29884480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60817664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60817664 = ⟨515499241, 1381433871⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30408832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61341760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61341760 = ⟨197896186, 1538329412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30670880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63438912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63438912 = ⟨1499706608, 298914685⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31719456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63963264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63963264 = ⟨1364616218, 1766355446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31981632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65536064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65536064 = ⟨2050363158, 1363794924⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32768032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_68157568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 68157568 = ⟨1274793396, 8663487⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34078784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69206272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69206272 = ⟨262555526, 1305668337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34603136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71303680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71303680 = ⟨695693651, 1184408411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35651840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72351872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72351872 = ⟨48172579, 1874167821⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36175936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_75498496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 75498496 = ⟨1844375598, 1823771499⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37749248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76546176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76546176 = ⟨1360469272, 514093961⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38273088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77594880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77594880 = ⟨169186900, 164840510⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38797440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_80740480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 80740480 = ⟨1687517385, 1369342921⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40370240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_84934784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84934784 = ⟨1426897433, 405192596⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42467392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_85983488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 85983488 = ⟨1700686825, 1321217824⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42991744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88080896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88080896 = ⟨1015238489, 940024633⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44040448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89129088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89129088 = ⟨605891508, 540488400⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44564544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_93323392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93323392 = ⟨1519334438, 132352710⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46661696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94372096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94372096 = ⟨882780876, 152063747⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47186048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_97517696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 97517696 = ⟨314393984, 1492766378⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48758848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_101712000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101712000 = ⟨853904830, 1891170744⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50856000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102760704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102760704 = ⟨335259042, 1668214823⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51380352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104858112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104858112 = ⟨1680700037, 638207652⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52429056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105906304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105906304 = ⟨318229844, 870702245⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52953152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_109052928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109052928 = ⟨1935941148, 1205027416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54526464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_110100608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110100608 = ⟨957150844, 727232942⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55050304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_111149312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 111149312 = ⟨18342679, 1360448874⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55574656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_114294912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114294912 = ⟨1999810106, 1370429191⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57147456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_118489216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118489216 = ⟨508415458, 404362452⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59244608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_119537920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119537920 = ⟨1302078791, 1979303648⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59768960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121635328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121635328 = ⟨295967406, 54684233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60817664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122683520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122683520 = ⟨596953620, 1497033975⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61341760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126877824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126877824 = ⟨534686865, 16569155⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63438912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_127926528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 127926528 = ⟨546817863, 1054155833⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63963264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_131072128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131072128 = ⟨364212982, 1933633861⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65536064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_136315136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 136315136 = ⟨1387894257, 1756941567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68157568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_138412544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 138412544 = ⟨391828945, 2025014118⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69206272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_142607360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 142607360 = ⟨1636215277, 965201017⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71303680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_144703744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 144703744 = ⟨1537518553, 640524545⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72351872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_153092352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 153092352 = ⟨1106996861, 477357809⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76546176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_155189760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 155189760 = ⟨632544609, 307610560⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77594880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_161480960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 161480960 = ⟨1409454637, 918007457⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80740480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_169869568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 169869568 = ⟨407272892, 1676459734⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84934784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_171966976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 171966976 = ⟨767542279, 1500905900⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85983488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_176161792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 176161792 = ⟨1150508049, 626837953⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88080896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_178258176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 178258176 = ⟨819776405, 1845432343⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89129088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_186646784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 186646784 = ⟨172682848, 340477126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93323392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_188744192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 188744192 = ⟨556904846, 319983437⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94372096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_195035392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 195035392 = ⟨1765353173, 1279767157⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_97517696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_203424000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 203424000 = ⟨1632081627, 310128572⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101712000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_205521408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 205521408 = ⟨199867608, 796925715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102760704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_209716224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 209716224 = ⟨1489475671, 1590331411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104858112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_211812608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 211812608 = ⟨1596877333, 1006675446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105906304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_220201216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 220201216 = ⟨885010892, 1046105697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110100608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_222298624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 222298624 = ⟨187457572, 1087472685⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111149312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_228589824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 228589824 = ⟨1081502290, 528625958⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114294912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_236978432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 236978432 = ⟨2104018592, 374985981⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118489216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_239075840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 239075840 = ⟨839412234, 1410951442⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119537920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_243270656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 243270656 = ⟨541880188, 1280134915⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121635328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_245367040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 245367040 = ⟨286210574, 677281329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122683520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_253755648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 253755648 = ⟨1266487852, 2096840672⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126877824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_255853056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 255853056 = ⟨1918638746, 1405635136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_127926528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_262144256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 262144256 = ⟨1179983527, 623629249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131072128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_272630272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 272630272 = ⟨1328972835, 1987919950⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_136315136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_276825088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 276825088 = ⟨932754395, 1184859162⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_138412544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_289407488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 289407488 = ⟨1375808581, 1684366863⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_144703744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_306184704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 306184704 = ⟨1772217926, 1066541459⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_153092352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_310379520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 310379520 = ⟨1415786230, 1111815158⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_155189760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_322961920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 322961920 = ⟨916289442, 1780109444⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_161480960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_339739136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 339739136 = ⟨173502480, 419700001⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_169869568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_343933952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 343933952 = ⟨1036868259, 1302232773⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_171966976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_356516352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 356516352 = ⟨2034857098, 703593348⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_178258176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_373293568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 373293568 = ⟨1553271351, 1779384796⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_186646784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_377488384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 377488384 = ⟨809155383, 303944815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_188744192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_390070784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 390070784 = ⟨1115395302, 667775390⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_195035392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_406848000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 406848000 = ⟨211554318, 919265624⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_203424000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_411042816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 411042816 = ⟨993237774, 289789953⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_205521408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_423625216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 423625216 = ⟨1351661577, 1932487841⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_211812608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_440402432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 440402432 = ⟨1658455861, 517122998⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_220201216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_444597248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 444597248 = ⟨317286896, 920117449⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_222298624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_457179648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 457179648 = ⟨544060484, 1860137440⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_228589824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_473956864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 473956864 = ⟨1844820841, 824026006⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_236978432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_478151680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 478151680 = ⟨271955858, 2011039234⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_239075840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_490734080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 490734080 = ⟨1915276285, 302298533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_245367040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_507511296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 507511296 = ⟨1770948129, 2139365904⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_253755648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_511706112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 511706112 = ⟨1598024857, 1875094528⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_255853056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_524288512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 524288512 = ⟨846054948, 399696236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_262144256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_545260544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 545260544 = ⟨469433912, 1746898694⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_272630272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_578814976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 578814976 = ⟨292984488, 1652551137⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_289407488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_612369408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 612369408 = ⟨1823771499, 303108049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_306184704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_645923840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 645923840 = ⟨1205027416, 211542499⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_322961920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_679478272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 679478272 = ⟨965201017, 511268370⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_339739136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_713032704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 713032704 = ⟨626837953, 996975598⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_356516352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_746587136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 746587136 = ⟨1590331411, 658007976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_373293568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_780141568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 780141568 = ⟨1280134915, 1605603459⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_390070784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_813696000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 813696000 = ⟨1184859162, 1214729252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_406848000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_847250432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 847250432 = ⟨1111815158, 731697417⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_423625216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_880804864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 880804864 = ⟨1302232773, 1110615388⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_440402432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_914359296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 914359296 = ⟨303944815, 1338328264⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_457179648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_947913728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 947913728 = ⟨289789953, 1154245873⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_473956864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_981468160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 981468160 = ⟨920117449, 1830196751⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_490734080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1015022592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1015022592 = ⟨2011039234, 1875527789⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_507511296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1048577024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1048577024 = ⟨1875094528, 549458790⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_524288512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 64) = ⟨400584953, 469433912⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 64 = 8389632 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_8389632

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨400584953, 469433912⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 64) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 65) = ⟨469433912, 1746898694⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 65 = 545260544 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_545260544

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨469433912, 1746898694⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 65) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 66) = ⟨932754395, 1184859162⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 66 = 276825088 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_276825088

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨932754395, 1184859162⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 66) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 67) = ⟨1184859162, 1214729252⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 67 = 813696000 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_813696000

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1184859162, 1214729252⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 67) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 68) = ⟨1636215277, 965201017⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 68 = 142607360 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_142607360

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1636215277, 965201017⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 68) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 69) = ⟨965201017, 511268370⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 69 = 679478272 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_679478272

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨965201017, 511268370⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 69) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 70) = ⟨993237774, 289789953⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 70 = 411042816 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_411042816

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨993237774, 289789953⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 70) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 71) = ⟨289789953, 1154245873⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 71 = 947913728 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_947913728

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨289789953, 1154245873⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 71) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 72) = ⟨1844375598, 1823771499⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 72 = 75498496 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_75498496

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1844375598, 1823771499⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 72) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 73) = ⟨1823771499, 303108049⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 73 = 612369408 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_612369408

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1823771499, 303108049⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 73) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 74) = ⟨1036868259, 1302232773⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 74 = 343933952 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_343933952

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1036868259, 1302232773⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 74) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 75) = ⟨1302232773, 1110615388⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 75 = 880804864 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_880804864

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1302232773, 1110615388⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 75) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 76) = ⟨1489475671, 1590331411⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 76 = 209716224 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_209716224

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1489475671, 1590331411⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 76) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 77) = ⟨1590331411, 658007976⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 77 = 746587136 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_746587136

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1590331411, 658007976⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 77) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 78) = ⟨271955858, 2011039234⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 78 = 478151680 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_478151680

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨271955858, 2011039234⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 78) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 79) = ⟨2011039234, 1875527789⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 79 = 1015022592 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1015022592

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2011039234, 1875527789⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 79) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 80) = ⟨494932510, 292984488⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 80 = 41944064 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_41944064

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨494932510, 292984488⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 80) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 81) = ⟨292984488, 1652551137⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 81 = 578814976 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_578814976

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨292984488, 1652551137⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 81) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 82) = ⟨1415786230, 1111815158⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 82 = 310379520 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_310379520

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1415786230, 1111815158⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 82) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 83) = ⟨1111815158, 731697417⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 83 = 847250432 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_847250432

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1111815158, 731697417⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 83) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 84) = ⟨1150508049, 626837953⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 84 = 176161792 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_176161792

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1150508049, 626837953⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 84) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 85) = ⟨626837953, 996975598⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 85 = 713032704 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_713032704

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨626837953, 996975598⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 85) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 86) = ⟨317286896, 920117449⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 86 = 444597248 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_444597248

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨317286896, 920117449⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 86) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 87) = ⟨920117449, 1830196751⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 87 = 981468160 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_981468160

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨920117449, 1830196751⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 87) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 88) = ⟨1935941148, 1205027416⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 88 = 109052928 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_109052928

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1935941148, 1205027416⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 88) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 89) = ⟨1205027416, 211542499⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 89 = 645923840 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_645923840

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1205027416, 211542499⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 89) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 90) = ⟨809155383, 303944815⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 90 = 377488384 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_377488384

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨809155383, 303944815⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 90) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 91) = ⟨303944815, 1338328264⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 91 = 914359296 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_914359296

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨303944815, 1338328264⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 91) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 92) = ⟨541880188, 1280134915⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 92 = 243270656 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_243270656

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨541880188, 1280134915⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 92) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 93) = ⟨1280134915, 1605603459⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 93 = 780141568 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_780141568

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1280134915, 1605603459⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 93) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 94) = ⟨1598024857, 1875094528⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 94 = 511706112 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_511706112

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1598024857, 1875094528⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 94) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 95) = ⟨1875094528, 549458790⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 95 = 1048577024 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1048577024

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1875094528, 549458790⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 95) := by
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

end R17TableAChunk02Certificate
