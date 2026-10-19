import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableBChunk02Certificate
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

theorem power_8192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8192 = ⟨1799120754, 343598868⟩ := by
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

theorem power_16384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16384 = ⟨438833264, 1327019128⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8192]
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

theorem power_40960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40960 = ⟨263253631, 1948074535⟩ := by
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

theorem power_73728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73728 = ⟨124482577, 226221110⟩ := by
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

theorem power_81920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81920 = ⟨1635360495, 1075839836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40960]
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

theorem power_106496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106496 = ⟨1488671228, 939868393⟩ := by
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

theorem power_139264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 139264 = ⟨521340221, 1824173925⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_141312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 141312 = ⟨1719915550, 648525961⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_147456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 147456 = ⟨1384581133, 347627210⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73728]
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

theorem power_172032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 172032 = ⟨735504938, 198004457⟩ := by
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

theorem power_204800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 204800 = ⟨607954189, 1091734815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_206848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 206848 = ⟨1817546580, 1225707862⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_212992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 212992 = ⟨1004021208, 1870425365⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106496]
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

theorem power_237568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 237568 = ⟨474711937, 1020011657⟩ := by
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

theorem power_266240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 266240 = ⟨2008329732, 1737289791⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_270336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 270336 = ⟨844712212, 1454882131⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_135168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_278528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 278528 = ⟨694768587, 1335510377⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_139264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_282624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 282624 = ⟨18918067, 521344418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_141312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_299008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 299008 = ⟨1318914216, 1663922738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_149504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_303104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 303104 = ⟨1479292912, 403634516⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_151552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_315392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 315392 = ⟨1576856103, 1461690978⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_157696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_331776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 331776 = ⟨1250840269, 386418603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_165888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_335872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 335872 = ⟨530115096, 90442098⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_167936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_344064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 344064 = ⟨2128165408, 1866558246⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_172032]
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

theorem power_368640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 368640 = ⟨1362074261, 2047718881⟩ := by
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

theorem power_401408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 401408 = ⟨245650224, 1174726897⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_200704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_409600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 409600 = ⟨1971845238, 153904061⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_204800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_413696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 413696 = ⟨1936661821, 241049853⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_206848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_430080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 430080 = ⟨782570832, 476532960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_215040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_434176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 434176 = ⟨386684296, 1363813538⟩ := by
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

theorem power_466944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 466944 = ⟨1055871441, 345775465⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_233472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_475136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 475136 = ⟨1461783988, 258760706⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_237568]
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

theorem power_499712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 499712 = ⟨836848068, 529120781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_249856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_512000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 512000 = ⟨1615674956, 1808914239⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_256000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_532480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 532480 = ⟨666420564, 2135132831⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_266240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_540672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 540672 = ⟨287625694, 714961257⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_270336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_565248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 565248 = ⟨153716819, 2054656334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_282624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_598016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 598016 = ⟨1564877543, 99597748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_299008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_606208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 606208 = ⟨116111969, 557501350⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_303104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_630784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 630784 = ⟨1542296538, 1163978019⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_315392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_663552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 663552 = ⟨1714778873, 1735902582⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_331776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_671744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 671744 = ⟨1421431969, 974095169⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_335872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_696320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 696320 = ⟨2083960347, 2126322313⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_348160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_729088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 729088 = ⟨1478673705, 1008068784⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_364544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_737280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 737280 = ⟨991418403, 1480232698⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_368640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_761856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 761856 = ⟨1739468984, 977169647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_380928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_794624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 794624 = ⟨292417279, 377436135⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_397312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_802816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 802816 = ⟨1684659278, 1370520300⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_401408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_827392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 827392 = ⟨682480399, 799350698⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_413696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_860160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 860160 = ⟨399207028, 155898355⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_430080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_868352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 868352 = ⟨720638041, 1133563860⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_434176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_892928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 892928 = ⟨1834599352, 1895440138⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_446464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_925696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 925696 = ⟨1606261854, 1606869623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_462848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_933888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 933888 = ⟨1923810989, 1272366406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_466944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_958464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 958464 = ⟨1439180125, 915904269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_479232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_991232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 991232 = ⟨881168337, 157473534⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_495616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_999424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 999424 = ⟨913493534, 2126309379⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_499712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1024000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1024000 = ⟨581559614, 117257650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_512000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1064960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1064960 = ⟨1247546638, 2100838754⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_532480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1130496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1130496 = ⟨330063644, 208626297⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_565248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1196032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1196032 = ⟨1780251437, 1948453877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_598016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1261568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1261568 = ⟨706427304, 2023867009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_630784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1327104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1327104 = ⟨414447487, 1660191568⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_663552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1392640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1392640 = ⟨1794178592, 2103779454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_696320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1458176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1458176 = ⟨1188557366, 413281552⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_729088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1523712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1523712 = ⟨1321308009, 1742025967⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_761856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1589248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1589248 = ⟨155805646, 741953977⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_794624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1654784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1654784 = ⟨1516934575, 1368952111⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_827392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1720320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1720320 = ⟨961627178, 109177970⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_860160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1785856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1785856 = ⟨1912203537, 1288850576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_892928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1851392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1851392 = ⟨467042048, 2131513571⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_925696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1916928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1916928 = ⟨1149377722, 1799983014⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_958464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1982464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1982464 = ⟨2063888815, 129056561⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_991232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2048000 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2048000 = ⟨1963867290, 360941673⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1024000]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 64) = ⟨438833264, 1327019128⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 64 = 16384 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_16384

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨438833264, 1327019128⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 64) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 65) = ⟨1247546638, 2100838754⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 65 = 1064960 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1064960

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1247546638, 2100838754⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 65) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 66) = ⟨287625694, 714961257⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 66 = 540672 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_540672

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨287625694, 714961257⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 66) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 67) = ⟨155805646, 741953977⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 67 = 1589248 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1589248

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨155805646, 741953977⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 67) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 68) = ⟨694768587, 1335510377⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 68 = 278528 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_278528

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨694768587, 1335510377⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 68) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 69) = ⟨414447487, 1660191568⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 69 = 1327104 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1327104

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨414447487, 1660191568⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 69) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 70) = ⟨1684659278, 1370520300⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 70 = 802816 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_802816

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1684659278, 1370520300⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 70) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 71) = ⟨467042048, 2131513571⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 71 = 1851392 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1851392

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨467042048, 2131513571⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 71) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 72) = ⟨1384581133, 347627210⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 72 = 147456 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_147456

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1384581133, 347627210⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 72) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 73) = ⟨1780251437, 1948453877⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 73 = 1196032 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1196032

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1780251437, 1948453877⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 73) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 74) = ⟨1421431969, 974095169⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 74 = 671744 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_671744

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1421431969, 974095169⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 74) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 75) = ⟨961627178, 109177970⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 75 = 1720320 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1720320

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨961627178, 109177970⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 75) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 76) = ⟨1971845238, 153904061⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 76 = 409600 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_409600

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1971845238, 153904061⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 76) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 77) = ⟨1188557366, 413281552⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 77 = 1458176 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1458176

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1188557366, 413281552⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 77) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 78) = ⟨1923810989, 1272366406⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 78 = 933888 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_933888

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1923810989, 1272366406⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 78) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 79) = ⟨2063888815, 129056561⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 79 = 1982464 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1982464

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2063888815, 129056561⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 79) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 80) = ⟨1635360495, 1075839836⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 80 = 81920 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_81920

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1635360495, 1075839836⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 80) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 81) = ⟨330063644, 208626297⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 81 = 1130496 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1130496

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨330063644, 208626297⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 81) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 82) = ⟨116111969, 557501350⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 82 = 606208 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_606208

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨116111969, 557501350⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 82) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 83) = ⟨1516934575, 1368952111⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 83 = 1654784 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1654784

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1516934575, 1368952111⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 83) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 84) = ⟨2128165408, 1866558246⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 84 = 344064 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_344064

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2128165408, 1866558246⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 84) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 85) = ⟨1794178592, 2103779454⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 85 = 1392640 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1392640

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1794178592, 2103779454⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 85) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 86) = ⟨720638041, 1133563860⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 86 = 868352 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_868352

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨720638041, 1133563860⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 86) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 87) = ⟨1149377722, 1799983014⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 87 = 1916928 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1916928

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1149377722, 1799983014⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 87) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 88) = ⟨1004021208, 1870425365⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 88 = 212992 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_212992

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1004021208, 1870425365⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 88) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 89) = ⟨706427304, 2023867009⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 89 = 1261568 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1261568

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨706427304, 2023867009⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 89) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 90) = ⟨991418403, 1480232698⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 90 = 737280 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_737280

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨991418403, 1480232698⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 90) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 91) = ⟨1912203537, 1288850576⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 91 = 1785856 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1785856

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1912203537, 1288850576⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 91) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 92) = ⟨1461783988, 258760706⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 92 = 475136 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_475136

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1461783988, 258760706⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 92) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 93) = ⟨1321308009, 1742025967⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 93 = 1523712 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1523712

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1321308009, 1742025967⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 93) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 94) = ⟨913493534, 2126309379⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 94 = 999424 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_999424

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨913493534, 2126309379⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 94) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.rightExponent 95) = ⟨1963867290, 360941673⟩ := by
  have hexp : R17TableExponentDomainBridge.rightExponent 95 = 2048000 := by
    norm_num [R17TableExponentDomainBridge.rightExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_2048000

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1963867290, 360941673⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.rightExponent 95) := by
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

end R17TableBChunk02Certificate
