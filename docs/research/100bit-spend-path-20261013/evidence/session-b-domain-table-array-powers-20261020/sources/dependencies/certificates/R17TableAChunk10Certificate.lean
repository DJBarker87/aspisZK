import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk10Certificate
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

theorem power_69 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69 = ⟨878709433, 901181160⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34]
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

theorem power_101 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101 = ⟨1779769850, 1133066291⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50]
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

theorem power_130 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 130 = ⟨182745460, 1218067210⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_133 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 133 = ⟨697736105, 1609499589⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_138 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 138 = ⟨289576174, 117745875⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69]
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

theorem power_149 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 149 = ⟨1021562393, 1112546712⟩ := by
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

theorem power_165 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 165 = ⟨1912338015, 1472102703⟩ := by
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

theorem power_181 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 181 = ⟨1696217250, 537553639⟩ := by
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

theorem power_197 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 197 = ⟨929859587, 264346242⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_202 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 202 = ⟨1860360142, 751729554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101]
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

theorem power_213 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 213 = ⟨1005480520, 1074898100⟩ := by
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

theorem power_229 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 229 = ⟨1000103727, 1053059015⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114]
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

theorem power_245 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 245 = ⟨58842794, 1641594984⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_250 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 250 = ⟨1254622717, 393467164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_261 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 261 = ⟨887095529, 705445016⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_130]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_266 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 266 = ⟨1886029052, 1532389385⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_276 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 276 = ⟨2136981225, 76442191⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_138]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_277 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 277 = ⟨1590010471, 1669341117⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_138]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_293 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 293 = ⟨544209909, 805215206⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_146]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 296 = ⟨224965265, 159335170⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_148]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_298 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 298 = ⟨1987234348, 1575849251⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_149]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_309 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 309 = ⟨1773322170, 1401860531⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_154]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 320 = ⟨1637047685, 109864373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_325 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 325 = ⟨877962113, 214735620⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_162]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_330 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 330 = ⟨499846262, 739901923⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_165]
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

theorem power_341 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 341 = ⟨1827617895, 657241266⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_170]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_357 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 357 = ⟨2120071580, 258855831⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_178]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_362 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 362 = ⟨1653955205, 1266544038⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_181]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_373 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 373 = ⟨2054288897, 415877199⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_186]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_389 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 389 = ⟨1119546319, 1056662496⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_194]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_394 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 394 = ⟨1502978530, 1510529028⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_197]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_404 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 404 = ⟨1264991587, 1665650581⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_202]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_405 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 405 = ⟨814542909, 1862091911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_202]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_421 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 421 = ⟨53821688, 150435782⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_210]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 424 = ⟨167179466, 382336254⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_212]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_426 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 426 = ⟨740193435, 419472664⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_213]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_437 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 437 = ⟨787272897, 673996239⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_218]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_453 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 453 = ⟨158037504, 792625753⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_226]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_458 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 458 = ⟨1423811280, 1075984596⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_229]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_468 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 468 = ⟨2093397897, 1522550679⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_234]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_469 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 469 = ⟨589857307, 324973244⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_234]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_485 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 485 = ⟨402563157, 99161364⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_242]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_490 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 490 = ⟨1244644911, 1069588596⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_245]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_501 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 501 = ⟨466104544, 234312091⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_250]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_522 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 522 = ⟨724613538, 1996712280⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_261]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_532 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 532 = ⟨285160156, 357127343⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_266]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 552 = ⟨1478094092, 46019520⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_276]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_554 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 554 = ⟨124779070, 1904095122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_277]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_586 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 586 = ⟨2102489303, 1825747639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_293]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 592 = ⟨462102546, 1660293932⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_596 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 596 = ⟨1491797637, 1365652507⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_298]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_618 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 618 = ⟨856596127, 1433324757⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_309]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 640 = ⟨982766847, 1369509443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_650 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 650 = ⟨1693779873, 1488092473⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_325]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_660 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 660 = ⟨224203845, 414234931⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_330]
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

theorem power_682 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 682 = ⟨915393797, 1370929172⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_341]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_714 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 714 = ⟨1565999672, 131526384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_357]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_724 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 724 = ⟨1031951347, 729196118⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_362]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_746 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 746 = ⟨80944339, 1337339394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_373]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_778 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 778 = ⟨1100417802, 1192490472⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_389]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_788 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 788 = ⟨1950981915, 1375812553⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_394]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 808 = ⟨1343024069, 808079406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_404]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_810 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 810 = ⟨757693387, 755639905⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_405]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_842 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 842 = ⟨243469030, 1472864070⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_421]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 848 = ⟨639667341, 414959610⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_852 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 852 = ⟨1095473796, 1598161515⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_426]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_874 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 874 = ⟨1136152890, 90232497⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_437]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_906 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 906 = ⟨908783006, 1602497009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_453]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_916 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 916 = ⟨1977654507, 446409834⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_458]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 936 = ⟨977714903, 1051251569⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_468]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_938 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 938 = ⟨745489826, 283422711⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_469]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_970 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 970 = ⟨791392440, 889734837⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_485]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_980 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 980 = ⟨1801197367, 627878655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_490]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1002 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1002 = ⟨1522066285, 1772680502⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_501]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1044 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1044 = ⟨1004319633, 1877174761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_522]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1064 = ⟨1028189478, 1432821515⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_532]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1104 = ⟨1224066945, 216858013⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1108 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1108 = ⟨899649712, 936678025⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_554]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1172 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1172 = ⟨351809933, 1227640569⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_586]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1184 = ⟨1392219141, 868524623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1192 = ⟨1278915379, 156031814⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_596]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1236 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1236 = ⟨1410637221, 1844259786⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_618]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1280 = ⟨1774187400, 1713497086⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1300 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1300 = ⟨1678362743, 375331126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_650]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1320 = ⟨2118388939, 778673083⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_660]
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

theorem power_1364 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1364 = ⟨1175580996, 804584992⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_682]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1428 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1428 = ⟨243525611, 332090494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_714]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1448 = ⟨331639486, 137962451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_724]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1492 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1492 = ⟨1048496077, 766417586⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_746]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1556 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1556 = ⟨2009328555, 1966680890⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_778]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1576 = ⟨64769829, 707320841⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_788]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1616 = ⟨190241594, 1357019236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1620 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1620 = ⟨564385514, 869558385⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_810]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1684 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1684 = ⟨587198044, 1194172746⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_842]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1696 = ⟨797688518, 1724894293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1704 = ⟨533992267, 1222429731⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_852]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1748 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1748 = ⟨972259116, 31336498⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_874]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1812 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1812 = ⟨648308941, 1555534908⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_906]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1832 = ⟨1811599737, 1651618790⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_916]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1872 = ⟨1690319162, 1749624555⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1876 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1876 = ⟨1773352507, 875983512⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_938]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1940 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1940 = ⟨1918849504, 2063780891⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_970]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1960 = ⟨190729669, 1803211581⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_980]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2004 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2004 = ⟨906956435, 673540617⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1002]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2088 = ⟨576066665, 484003135⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1044]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2128 = ⟨1959664240, 1343172434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2208 = ⟨1676955329, 1180692240⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2216 = ⟨96126839, 1478023181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1108]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2344 = ⟨745369801, 326364497⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1172]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2368 = ⟨39852141, 123936243⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2384 = ⟨1273255873, 638520824⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2472 = ⟨70106407, 325773505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1236]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2560 = ⟨1743980363, 345791924⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2600 = ⟨1997464212, 2089931530⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1300]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2640 = ⟨974359725, 754960039⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1320]
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

theorem power_2728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2728 = ⟨160004332, 895527120⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1364]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2856 = ⟨1149413572, 1354438634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1428]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2896 = ⟨754893878, 907943051⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2984 = ⟨1753174675, 1240998222⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1492]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3112 = ⟨319403162, 829776308⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1556]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3152 = ⟨2086360188, 1335899009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3232 = ⟨124445571, 706631523⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3240 = ⟨2122233045, 470814580⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1620]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3368 = ⟨1704087251, 554329542⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1684]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3392 = ⟨968612238, 1641022910⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3408 = ⟨1328324961, 803287742⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3496 = ⟨1038268432, 618423347⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1748]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3624 = ⟨846416670, 458184283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1812]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3664 = ⟨430184902, 2122941069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3744 = ⟨103855733, 1898302976⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3752 = ⟨1049617143, 1346140824⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1876]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3880 = ⟨155396518, 1844213334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1940]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3920 = ⟨1184704737, 1073695025⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4008 = ⟨566639860, 227001783⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2004]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4176 = ⟨1254428567, 1344369642⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4256 = ⟨1931712912, 754673528⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4416 = ⟨408933184, 381501510⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4432 = ⟨892322533, 63184316⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4688 = ⟨1217147354, 2016182289⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4736 = ⟨272617121, 579551580⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4768 = ⟨1639439199, 2098400799⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4944 = ⟨121049142, 593392617⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5120 = ⟨235158087, 2112924242⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5200 = ⟨787392813, 1242417377⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5280 = ⟨1521143491, 1687728277⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2640]
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

theorem power_5456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5456 = ⟨2094531691, 1594785536⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5712 = ⟨905600383, 502487204⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5792 = ⟨582466233, 38339503⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5968 = ⟨462932604, 1282839941⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6224 = ⟨572759547, 939328932⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6304 = ⟨162898390, 1970049448⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6464 = ⟨976698970, 920955611⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6480 = ⟨1423201619, 1713112157⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6736 = ⟨521509652, 1399872874⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6784 = ⟨1220597866, 72538165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6816 = ⟨1545116424, 2064043564⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6992 = ⟨2097501187, 1195801125⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7248 = ⟨1036133400, 444251496⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7328 = ⟨1926652717, 428844655⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7488 = ⟨1416522298, 2020079164⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7504 = ⟨931012573, 23587777⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7760 = ⟨11295097, 1501404992⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7840 = ⟨988509914, 508843856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8016 = ⟨297362948, 2075563960⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8352 = ⟨1846290674, 2127401616⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8512 = ⟨1109321131, 138320471⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8832 = ⟨2028834280, 858819348⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8864 = ⟨421462049, 1075272309⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9376 = ⟨847707788, 1604447739⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9472 = ⟨2016094574, 1147504298⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9536 = ⟨1288616871, 1536669085⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9888 = ⟨1497747890, 1248905498⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10241 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10241 = ⟨362341607, 867373160⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10400 = ⟨2036035837, 1354481791⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10560 = ⟨1013382771, 1429471715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5280]
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

theorem power_10912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10912 = ⟨751760303, 1937971085⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11424 = ⟨1441368134, 661375603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11584 = ⟨1412692279, 676395092⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11936 = ⟨1489326841, 1219763615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12448 = ⟨309695454, 1539951402⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12608 = ⟨391042756, 974739797⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12928 = ⟨2024521721, 865260240⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12960 = ⟨1010864705, 443556089⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13472 = ⟨1569417381, 1117228252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13568 = ⟨1050297291, 98481735⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13632 = ⟨1665935276, 1734295473⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13984 = ⟨395886768, 1585232512⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14496 = ⟨243656248, 930484996⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14656 = ⟨1633565514, 1655430508⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14976 = ⟨2067447709, 1097691368⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15008 = ⟨1596213474, 431611167⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15520 = ⟨867993218, 1886128439⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15680 = ⟨487689472, 284064100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16032 = ⟨1237776227, 953040654⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16704 = ⟨1739774103, 1375699924⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17024 = ⟨1619953932, 346710098⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17664 = ⟨15796839, 1693524553⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17728 = ⟨2111328158, 1636007152⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18752 = ⟨2000176023, 1738446810⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18944 = ⟨83021569, 1776986900⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19072 = ⟨1087399768, 299521376⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19776 = ⟨1878440681, 286140753⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20482 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20482 = ⟨289559643, 1599283009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10241]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20800 = ⟨1167522293, 1558834292⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21120 = ⟨169513512, 2043020633⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10560]
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

theorem power_21824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21824 = ⟨445812614, 2075887292⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22848 = ⟨457215079, 776857634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23168 = ⟨466922503, 476127114⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23872 = ⟨2002645233, 485051574⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24896 = ⟨1912366133, 673970933⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25216 = ⟨531994522, 589272094⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25856 = ⟨1354554672, 1833839332⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25920 = ⟨282442849, 535858663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26944 = ⟨1755532412, 705403472⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27136 = ⟨698096929, 432547149⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27264 = ⟨1385933946, 1155521422⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27968 = ⟨214182163, 504809403⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28992 = ⟨1304233307, 747724489⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29312 = ⟨1816695102, 1289326046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29952 = ⟨1852134147, 634458272⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30016 = ⟨772774905, 1367495886⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31040 = ⟨1829459389, 352858326⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31360 = ⟨478538903, 11590567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32064 = ⟨2037690233, 878027367⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33408 = ⟨2122051343, 1502584936⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34048 = ⟨923306421, 1161192049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35328 = ⟨750253747, 530937643⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35456 = ⟨1983487267, 2049490266⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37504 = ⟨1776694002, 486095290⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37888 = ⟨451882769, 1853894340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38144 = ⟨1930645967, 1155688905⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39552 = ⟨1617321897, 1666398552⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40964 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40964 = ⟨1712796223, 718520288⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20482]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41600 = ⟨771749905, 1789894681⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42240 = ⟨1220257075, 155758384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43009 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43009 = ⟨1467212999, 148910839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43520 = ⟨1133865341, 1051269249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43648 = ⟨94787716, 447126738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45696 = ⟨10246770, 1229819079⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46336 = ⟨1048380476, 1956147418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47744 = ⟨1583310758, 88074538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49792 = ⟨1042680611, 573138077⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50432 = ⟨449576803, 1250724952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51712 = ⟨554838094, 2082603647⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51840 = ⟨1283383677, 260284195⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53888 = ⟨613945693, 1702567950⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54272 = ⟨1176403617, 782773078⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54528 = ⟨1518385385, 591293547⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55936 = ⟨1776949107, 666110536⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57984 = ⟨727867352, 1912194038⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58624 = ⟨1640223361, 1258059286⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59904 = ⟨486461911, 1395218254⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60032 = ⟨1704027237, 352844513⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62080 = ⟨330610976, 281011390⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62720 = ⟨2077215075, 695458097⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64128 = ⟨643521186, 2074454300⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66816 = ⟨826733324, 1632054927⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_68096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 68096 = ⟨102310340, 81272348⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_70656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70656 = ⟨1921779281, 131885⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_70912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70912 = ⟨376999137, 186728435⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_75008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 75008 = ⟨1630629040, 535225621⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_75777 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 75777 = ⟨606522874, 1463409782⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76288 = ⟨1084669591, 1925834344⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_79104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 79104 = ⟨1309244894, 808238414⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_81928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81928 = ⟨758599571, 163377094⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40964]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_83200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83200 = ⟨1502467801, 2046812458⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_84480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84480 = ⟨954329647, 1601612428⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_86018 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86018 = ⟨704253244, 1600261087⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43009]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87040 = ⟨290570175, 898698902⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87296 = ⟨605402703, 508846547⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_91392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 91392 = ⟨902443904, 1665688026⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92672 = ⟨576129160, 699868407⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_95488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 95488 = ⟨159305208, 694935628⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_99584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 99584 = ⟨1108990402, 1908369643⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_100864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 100864 = ⟨1321798221, 991073372⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_103424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103424 = ⟨733457982, 495056491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_103680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103680 = ⟨1187004709, 88341746⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_107776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 107776 = ⟨606565484, 1348306984⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108545 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108545 = ⟨1609451271, 678835644⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_109056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109056 = ⟨85627671, 1011996137⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_111872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 111872 = ⟨470495359, 586073696⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115968 = ⟨1206703231, 780551149⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_117248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117248 = ⟨1418966850, 1211837697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_119808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119808 = ⟨1114403665, 611529715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120064 = ⟨1220693724, 848174215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124160 = ⟨1003476029, 1827409806⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_125440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 125440 = ⟨1284671812, 504899699⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_128256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128256 = ⟨1702992653, 1284805247⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_133632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 133632 = ⟨2022736880, 1076506197⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_136192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 136192 = ⟨437058642, 1419738284⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_141313 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 141313 = ⟨1784761065, 86582763⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_141824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 141824 = ⟨550600557, 706516473⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_150016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 150016 = ⟨1722018208, 2067876616⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_151554 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 151554 = ⟨1280339847, 1550123407⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75777]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_152576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 152576 = ⟨885008830, 1594173084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_158208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 158208 = ⟨505691453, 1353722632⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_79104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_163856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 163856 = ⟨264115333, 1961677940⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_166400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 166400 = ⟨180167, 121120669⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_168960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 168960 = ⟨1279156361, 1548443426⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_172036 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 172036 = ⟨1061584395, 122007771⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86018]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_174081 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 174081 = ⟨1730682582, 642797896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_174592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 174592 = ⟨1508724023, 686040406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_182784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 182784 = ⟨1307436064, 584602466⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_185344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 185344 = ⟨1809743850, 388676761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_190976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 190976 = ⟨756475306, 791775354⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_95488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_199168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 199168 = ⟨1451379096, 89833514⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_201728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 201728 = ⟨329561842, 1307878404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_206849 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 206849 = ⟨1043887770, 1808980585⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_207360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 207360 = ⟨1449029305, 1424764911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_215552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 215552 = ⟨807442027, 2078624134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_107776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_217090 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 217090 = ⟨1027382879, 1987794058⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108545]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_218112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 218112 = ⟨919013925, 1686206068⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_223744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 223744 = ⟨75336293, 1323001228⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_231936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 231936 = ⟨703205853, 1895369236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_234496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 234496 = ⟨29093893, 259327061⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_239617 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 239617 = ⟨65739397, 1278445154⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_240128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 240128 = ⟨237836669, 1673046321⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_248320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 248320 = ⟨1226571589, 1672604859⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_250880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 250880 = ⟨1374751140, 1733176008⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_125440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_256512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 256512 = ⟨1728288041, 66074390⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_267264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 267264 = ⟨1193162519, 1124194159⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_272385 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 272385 = ⟨59665217, 744809744⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_136192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_282626 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 282626 = ⟨1305340973, 259842299⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_141313]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_283648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 283648 = ⟨799200771, 1867442232⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_141824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_300032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 300032 = ⟨1384473723, 504239567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_150016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_303108 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 303108 = ⟨1961631833, 1500362736⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_151554]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_305153 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 305153 = ⟨1608580969, 2111951328⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_152576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_316416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 316416 = ⟨902713087, 146183753⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_158208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_327712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 327712 = ⟨503408729, 272213735⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_163856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_332800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 332800 = ⟨495786367, 584985465⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_166400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_337921 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 337921 = ⟨1073288077, 1650857024⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_168960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_344072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 344072 = ⟨1790230203, 1124688757⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_172036]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_348162 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 348162 = ⟨1534259759, 1972767704⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_174081]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_349184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 349184 = ⟨412856899, 1999546639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_174592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_365568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 365568 = ⟨1005971757, 209531419⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_182784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_370689 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 370689 = ⟨570077455, 1625922304⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_185344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_381952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 381952 = ⟨910648559, 1177238623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_190976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_398336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 398336 = ⟨1543455619, 121699991⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_199168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_403457 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 403457 = ⟨2021921706, 996992864⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_201728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_413698 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 413698 = ⟨555892962, 1842017849⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_206849]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_414720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 414720 = ⟨202201161, 1890408873⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_207360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_431104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 431104 = ⟨1249121193, 1115654910⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_215552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_434180 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 434180 = ⟨60462545, 32562128⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_217090]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_436225 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 436225 = ⟨854598954, 1539646619⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_218112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_447488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 447488 = ⟨859225919, 1389983192⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_223744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_463872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 463872 = ⟨33124487, 1071564562⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_231936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_468993 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 468993 = ⟨2136562679, 1463866442⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_234496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_479234 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 479234 = ⟨571997268, 762044645⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_239617]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_480256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 480256 = ⟨1276848383, 1622242922⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_240128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_496640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 496640 = ⟨901053382, 987411848⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_248320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_501761 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 501761 = ⟨2113063919, 77365794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_250880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_513024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 513024 = ⟨1301088625, 1743524387⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_256512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_534529 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 534529 = ⟨1170565379, 533491093⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_267264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_544770 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 544770 = ⟨1581868027, 1659844382⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_272385]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_565252 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 565252 = ⟨914364078, 327676948⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_282626]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_567297 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 567297 = ⟨1129715381, 867222864⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_283648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_600065 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 600065 = ⟨581005376, 1567766784⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_300032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_606216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 606216 = ⟨1979193939, 1646703629⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_303108]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_610306 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 610306 = ⟨1489485665, 1743792646⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_305153]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_632833 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 632833 = ⟨163064264, 15592934⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_316416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_655424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 655424 = ⟨1015427004, 421207605⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_327712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_665601 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 665601 = ⟨1361186901, 695495603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_332800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_675842 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 675842 = ⟨528654123, 1380924837⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_337921]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_688144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 688144 = ⟨1947004784, 262526936⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_344072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_696324 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 696324 = ⟨77428842, 534856291⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_348162]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_698369 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 698369 = ⟨1437384701, 1143588938⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_349184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_731137 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 731137 = ⟨425495475, 229391188⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_365568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_741378 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 741378 = ⟨1703795281, 1395276430⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_370689]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_763905 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 763905 = ⟨1209290906, 633793892⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_381952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_796673 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 796673 = ⟨956779131, 1260776686⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_398336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_806914 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 806914 = ⟨882226199, 568483892⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_403457]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_827396 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 827396 = ⟨840627269, 661825211⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_413698]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_829441 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 829441 = ⟨228420453, 470083094⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_414720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_862209 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 862209 = ⟨374775793, 1391278119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_431104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_868360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 868360 = ⟨2054544558, 1635976201⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_434180]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_872450 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 872450 = ⟨1624577263, 284110345⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_436225]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_894977 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 894977 = ⟨934520077, 1360619044⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_447488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_927745 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 927745 = ⟨1967039862, 64825777⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_463872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_937986 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 937986 = ⟨1190539875, 723041176⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_468993]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_958468 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 958468 = ⟨1371831349, 115786651⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_479234]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_960513 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 960513 = ⟨589679734, 34290766⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_480256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_993281 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 993281 = ⟨1450801052, 18905821⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_496640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1003522 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1003522 = ⟨679335929, 402134052⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_501761]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1026049 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1026049 = ⟨879716177, 1492345656⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_513024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1069058 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1069058 = ⟨460519275, 212551441⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_534529]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1089540 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1089540 = ⟨189536780, 244585778⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_544770]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1130504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1130504 = ⟨1584259879, 2137327604⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_565252]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1134594 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1134594 = ⟨1243081545, 570644880⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_567297]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1200130 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1200130 = ⟨1445805692, 260892037⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_600065]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1212432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1212432 = ⟨477941726, 1908843503⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_606216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1220612 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1220612 = ⟨182944569, 674720742⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_610306]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1265666 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1265666 = ⟨1310537263, 1354466683⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_632833]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1310848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1310848 = ⟨2091505399, 1680204714⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_655424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1331202 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1331202 = ⟨706200554, 719277466⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_665601]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1351684 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1351684 = ⟨2026403642, 1330383603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_675842]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1376288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1376288 = ⟨2001963155, 1925311962⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_688144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1392648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1392648 = ⟨1973701191, 478301876⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_696324]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1396738 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1396738 = ⟨244822100, 908314891⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_698369]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1462274 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1462274 = ⟨1607766343, 957561874⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_731137]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1482756 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1482756 = ⟨1677004474, 483778303⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_741378]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1527810 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1527810 = ⟨1947137300, 1239409950⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_763905]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1593346 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1593346 = ⟨261860273, 1466276690⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_796673]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1613828 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1613828 = ⟨505501427, 643144163⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_806914]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1654792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1654792 = ⟨493444663, 1518372915⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_827396]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1658882 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1658882 = ⟨1422172805, 757455649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_829441]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1724418 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1724418 = ⟨327058678, 1502213308⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_862209]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1736720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1736720 = ⟨81870574, 1004029869⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_868360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1744900 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1744900 = ⟨1096446590, 1919058794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_872450]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1789954 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1789954 = ⟨1370112320, 254558111⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_894977]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1855490 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1855490 = ⟨788262674, 712028577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_927745]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1875972 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1875972 = ⟨1460397533, 1448168893⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_937986]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1916936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1916936 = ⟨1464761233, 221537754⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_958468]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1921026 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1921026 = ⟨371063483, 237191657⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_960513]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1986562 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1986562 = ⟨663496220, 876542964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_993281]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2007044 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2007044 = ⟨2019206602, 1287509000⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1003522]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2052098 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2052098 = ⟨2127976719, 927756230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1026049]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2138116 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2138116 = ⟨1151147192, 14891586⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1069058]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2179080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2179080 = ⟨93021329, 1450372636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1089540]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2261008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2261008 = ⟨1155262417, 782386241⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1130504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2269188 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2269188 = ⟨2088865450, 194513390⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1134594]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2400260 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2400260 = ⟨565858313, 1901926274⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1200130]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2424864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2424864 = ⟨1012904529, 1540202147⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1212432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2441224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2441224 = ⟨303981531, 1493799878⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1220612]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2531332 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2531332 = ⟨1267923625, 1435650858⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1265666]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2621696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2621696 = ⟨269723734, 591706005⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1310848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2662404 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2662404 = ⟨1067703741, 642838514⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1331202]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2703368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2703368 = ⟨675292492, 570021376⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1351684]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2752576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2752576 = ⟨1658329532, 348202755⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1376288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2785296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2785296 = ⟨625513651, 953097913⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1392648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2793476 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2793476 = ⟨1550515145, 658322634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1396738]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2924548 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2924548 = ⟨1402000560, 570283117⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1462274]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2965512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2965512 = ⟨903319084, 105589979⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1482756]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3055620 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3055620 = ⟨68472584, 1556499413⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1527810]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3186692 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3186692 = ⟨918967265, 1587329108⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1593346]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3227656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3227656 = ⟨109815859, 1014546764⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1613828]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3309584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3309584 = ⟨1360595580, 950876091⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1654792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3317764 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3317764 = ⟨99596532, 1090509434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1658882]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3448836 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3448836 = ⟨1549619669, 1171926934⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1724418]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3473440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3473440 = ⟨1007127331, 1938240858⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1736720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3489800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3489800 = ⟨576005226, 89749754⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1744900]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3579908 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3579908 = ⟨1534581268, 1056369414⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1789954]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3710980 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3710980 = ⟨1805337067, 811706577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1855490]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3751944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3751944 = ⟨19569849, 387509246⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1875972]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3833872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3833872 = ⟨588976242, 504776899⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1916936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3842052 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3842052 = ⟨1468281756, 65674347⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1921026]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3973124 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3973124 = ⟨285779832, 733763532⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1986562]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4014088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4014088 = ⟨488666338, 1960152045⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2007044]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4104196 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4104196 = ⟨192784978, 1431074251⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2052098]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4276232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4276232 = ⟨1130424119, 21613207⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2138116]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4358160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4358160 = ⟨241838993, 1780277190⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2179080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4522016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4522016 = ⟨1024979319, 2105763026⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2261008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4538376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4538376 = ⟨2145460447, 962282401⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2269188]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4800520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4800520 = ⟨33128844, 266529684⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2400260]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4849728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4849728 = ⟨1369012400, 72161503⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2424864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4882448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4882448 = ⟨967795018, 1380643260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2441224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5062664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5062664 = ⟨564319273, 1927887466⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2531332]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5243392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5243392 = ⟨1525928955, 1276701483⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2621696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5324808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5324808 = ⟨147061550, 571467370⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2662404]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5406736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5406736 = ⟨1882098696, 2039563106⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2703368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5505152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5505152 = ⟨1481976989, 1986902624⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2752576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5570592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5570592 = ⟨131541136, 1347619193⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2785296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5586952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5586952 = ⟨1772342873, 1133679829⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2793476]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5849096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5849096 = ⟨444916072, 2044377457⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2924548]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5931024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5931024 = ⟨1459980440, 448778995⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2965512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6111240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6111240 = ⟨27164964, 37339682⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3055620]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6373384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6373384 = ⟨1039166372, 1374414857⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3186692]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6455312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6455312 = ⟨1953846426, 344460184⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3227656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6619168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6619168 = ⟨1880048757, 1887436963⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3309584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6635528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6635528 = ⟨1258047472, 1805339884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3317764]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6897672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6897672 = ⟨1394723272, 385587810⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3448836]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6946880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6946880 = ⟨1465922390, 1915794067⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3473440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6979600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6979600 = ⟨1234100156, 1493247276⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3489800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7159816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7159816 = ⟨1668667322, 2087448774⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3579908]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7421960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7421960 = ⟨1610807423, 1601484365⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3710980]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7503888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7503888 = ⟨2102488229, 761686454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3751944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7667744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7667744 = ⟨1568049909, 1351882392⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3833872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7684104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7684104 = ⟨238783365, 441948428⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3842052]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7946248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7946248 = ⟨782510754, 1535273102⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3973124]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8028176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8028176 = ⟨1358735721, 843438593⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4014088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8208392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8208392 = ⟨618278354, 989573793⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4104196]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8552464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8552464 = ⟨1326977653, 904708687⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4276232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8716320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8716320 = ⟨1916482416, 2009094989⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4358160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9044032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9044032 = ⟨882391009, 1032278041⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4522016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9076752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9076752 = ⟨468817635, 1334112001⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4538376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9601040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9601040 = ⟨937189856, 150675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4800520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9699456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9699456 = ⟨513072003, 257762950⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4849728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9764896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9764896 = ⟨1816697003, 1605925377⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4882448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10125328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10125328 = ⟨488465968, 369156957⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5062664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10486784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10486784 = ⟨894752084, 1749876144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5243392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10649616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10649616 = ⟨2118242164, 363918598⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5324808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10813472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10813472 = ⟨60066935, 1192625778⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5406736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11010304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11010304 = ⟨704339100, 1641813582⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5505152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11141184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11141184 = ⟨294684211, 1635096325⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5570592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11173904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11173904 = ⟨162649656, 339326841⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5586952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11698192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11698192 = ⟨1047330696, 1588930927⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5849096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11862048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11862048 = ⟨1408680023, 533316454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5931024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12222480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12222480 = ⟨1664423606, 1005275053⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6111240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12746768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12746768 = ⟨225891960, 1415670047⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6373384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12910624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12910624 = ⟨1432158992, 2039868348⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6455312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13238336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13238336 = ⟨876490288, 1298924658⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6619168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13271056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13271056 = ⟨1095322321, 1183768548⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6635528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13795344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13795344 = ⟨355667381, 2024639368⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6897672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13893760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13893760 = ⟨1960893939, 335832105⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6946880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13959200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13959200 = ⟨884822392, 1938636982⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6979600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14319632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14319632 = ⟨506286763, 362710244⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7159816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14843920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14843920 = ⟨913147810, 2137624609⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7421960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15007776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15007776 = ⟨376290479, 1766301123⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7503888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15335488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15335488 = ⟨1460632667, 496734147⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7667744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15368208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15368208 = ⟨1373219489, 1620818464⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7684104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15892496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15892496 = ⟨1599127402, 1543201279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7946248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16056352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16056352 = ⟨337848096, 146272113⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8028176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16416784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16416784 = ⟨1492081627, 1709724209⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8208392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17104928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17104928 = ⟨1011403152, 154222694⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8552464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17432640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17432640 = ⟨1271840770, 1810626965⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8716320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18088064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18088064 = ⟨1241361496, 1149620765⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9044032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18153504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18153504 = ⟨819790294, 644827304⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9076752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19202080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19202080 = ⟨1838728985, 146237689⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9601040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19398912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19398912 = ⟨234861078, 327554894⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9699456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19529792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19529792 = ⟨1034705420, 198709016⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9764896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20250656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20250656 = ⟨1821590555, 345497967⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10125328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21299232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21299232 = ⟨1528626597, 1416917468⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10649616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21626944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21626944 = ⟨25691287, 1364243772⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10813472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22020608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22020608 = ⟨39512066, 1835570716⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11010304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22282368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22282368 = ⟨272951801, 424851723⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11141184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22347808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22347808 = ⟨987450086, 308339215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11173904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23396384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23396384 = ⟨813979961, 521139181⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11698192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23724096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23724096 = ⟨831845724, 368576460⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11862048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24444960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24444960 = ⟨1955069204, 2069843190⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12222480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25493536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25493536 = ⟨930010185, 392616136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12746768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25821248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25821248 = ⟨623794511, 1996992578⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12910624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26476672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26476672 = ⟨2043664758, 277192417⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13238336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26542112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26542112 = ⟨146288937, 247155487⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13271056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27590688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27590688 = ⟨1488547241, 1438405692⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13795344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27787520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27787520 = ⟨416097272, 697514538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13893760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27918400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27918400 = ⟨1974478055, 324299631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13959200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28639264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28639264 = ⟨198875658, 557921861⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14319632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29687840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29687840 = ⟨1844057435, 739399471⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14843920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30015552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30015552 = ⟨537603362, 546519856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15007776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30670976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30670976 = ⟨1217572488, 1258143244⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15335488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30736416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30736416 = ⟨436620980, 484459877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15368208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31784992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31784992 = ⟨1219677675, 1388633080⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15892496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32112704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32112704 = ⟨2009830337, 1553239806⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16056352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32833568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32833568 = ⟨1666487934, 990251184⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16416784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34209856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34209856 = ⟨942649013, 1083260795⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17104928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34865280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34865280 = ⟨1480666610, 531665442⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17432640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36176128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36176128 = ⟨1769429792, 350333218⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18088064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36307008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36307008 = ⟨2085436344, 805763263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18153504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38404160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38404160 = ⟨1623036867, 430099489⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19202080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38797824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38797824 = ⟨41750961, 824030908⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19398912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39059584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39059584 = ⟨1795636458, 1250434549⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19529792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40501312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40501312 = ⟨1517489770, 943076505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20250656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42598464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42598464 = ⟨210081569, 1334014245⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21299232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43253888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43253888 = ⟨487818073, 2089926898⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21626944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44041216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44041216 = ⟨2003660710, 1164690642⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22020608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44564736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44564736 = ⟨140584850, 201977889⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22282368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44695616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44695616 = ⟨486274157, 727164121⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22347808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46792768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46792768 = ⟨680064231, 1890163888⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23396384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47448192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47448192 = ⟨1367073926, 907483747⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23724096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48889920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48889920 = ⟨1589586300, 555295441⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24444960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50987072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50987072 = ⟨697120363, 2144848575⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25493536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51642496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51642496 = ⟨816956821, 2839107⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25821248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52953344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52953344 = ⟨1257444884, 64500255⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26476672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53084224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53084224 = ⟨166825862, 1498529050⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26542112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55181376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55181376 = ⟨896973297, 133540438⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27590688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55575040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55575040 = ⟨1243081987, 1720231459⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27787520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55836800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55836800 = ⟨709721242, 1924964869⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27918400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57278528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57278528 = ⟨631382117, 1880100066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28639264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59375680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59375680 = ⟨1359793564, 183771050⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29687840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60031104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60031104 = ⟨1640833052, 274327199⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30015552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61341952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61341952 = ⟨1720035679, 1990955496⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30670976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61472832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61472832 = ⟨1004109232, 371529410⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30736416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63569984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63569984 = ⟨863022670, 10206874⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31784992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_64225408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 64225408 = ⟨251003911, 1280705999⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32112704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65667136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65667136 = ⟨947514730, 1530537318⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32833568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_68419712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 68419712 = ⟨1286909236, 394799718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34209856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69730560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69730560 = ⟨1945727554, 1043024715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34865280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72352256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72352256 = ⟨1579944344, 1789763405⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36176128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72614016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72614016 = ⟨1722305821, 1222316982⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36307008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76808320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76808320 = ⟨413792745, 1407910506⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38404160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77595648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77595648 = ⟨406765125, 1121751370⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38797824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_78119168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 78119168 = ⟨831602760, 2095815629⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39059584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_81002624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 81002624 = ⟨2011950889, 529240763⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40501312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_85196928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 85196928 = ⟨1970738182, 660434859⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42598464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_86507776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86507776 = ⟨1718230748, 2035538590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43253888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89129472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89129472 = ⟨1184660455, 1293252649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44564736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_89391232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 89391232 = ⟨727466645, 1208418859⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44695616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_93585536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93585536 = ⟨958310422, 1730371352⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46792768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94896384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94896384 = ⟨1229223568, 221244052⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47448192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_97779840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 97779840 = ⟨130395384, 1046377491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48889920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_101974144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101974144 = ⟨567854782, 1062363563⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50987072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_103284992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103284992 = ⟨102623132, 1070585349⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51642496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105906688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105906688 = ⟨1334092153, 1505737981⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52953344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106168448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106168448 = ⟨1863414882, 1068081641⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53084224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_110362752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110362752 = ⟨589163000, 917059341⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55181376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_111150080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 111150080 = ⟨834173210, 2010056637⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55575040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_111673600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 111673600 = ⟨243870370, 784366252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55836800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_114557056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114557056 = ⟨33284058, 1406128928⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57278528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_118751360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118751360 = ⟨774560034, 1846281273⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59375680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120062208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120062208 = ⟨1731354854, 2129976443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60031104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122683904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122683904 = ⟨1707361670, 1394860371⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61341952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122945664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122945664 = ⟨472028373, 1087516921⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61472832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_127139968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 127139968 = ⟨1194630071, 960408560⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63569984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_128450816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128450816 = ⟨109560787, 1016007179⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64225408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_131334272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131334272 = ⟨110700426, 5407115⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65667136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_136839424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 136839424 = ⟨680377995, 1682126447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68419712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_139461120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 139461120 = ⟨1491988707, 1743763813⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69730560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_144704512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 144704512 = ⟨1674153723, 1322319557⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72352256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_145228032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 145228032 = ⟨2000624371, 658157955⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72614016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_153616640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 153616640 = ⟨1018391295, 482843166⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76808320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_156238336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 156238336 = ⟨164355221, 1801980382⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78119168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_162005248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 162005248 = ⟨102494279, 790362394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_81002624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_170393856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 170393856 = ⟨232922893, 1494090293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85196928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_173015552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 173015552 = ⟨1739820147, 1683724639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86507776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_178258944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 178258944 = ⟨1894212231, 1899640059⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89129472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_178782464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 178782464 = ⟨305320937, 653999237⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89391232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_187171072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 187171072 = ⟨1912892893, 2089861190⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93585536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_189792768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 189792768 = ⟨2058525108, 400628072⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94896384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_195559680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 195559680 = ⟨1980629219, 2043372750⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_97779840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_203948288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 203948288 = ⟨2142983482, 1969910492⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101974144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_206569984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 206569984 = ⟨911964037, 415574339⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103284992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_211813376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 211813376 = ⟨336549856, 2103544920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105906688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_212336896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 212336896 = ⟨211450751, 1980280840⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_106168448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_220725504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 220725504 = ⟨1666156129, 318794188⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110362752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_223347200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 223347200 = ⟨1145587112, 2056388528⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111673600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_229114112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 229114112 = ⟨1518520712, 320760322⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114557056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_237502720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 237502720 = ⟨2146633175, 1215304043⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118751360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_240124416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 240124416 = ⟨1265691860, 739929951⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120062208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_245367808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 245367808 = ⟨703912353, 1783773358⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122683904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_245891328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 245891328 = ⟨2056537946, 2097701422⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122945664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_254279936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 254279936 = ⟨358030942, 1962870289⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_127139968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_256901632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 256901632 = ⟨89445513, 1591685143⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128450816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_262668544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 262668544 = ⟨46977714, 1486521713⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131334272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_273678848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 273678848 = ⟨1603512076, 194507045⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_136839424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_278922240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 278922240 = ⟨1770167713, 338572024⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_139461120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_290456064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 290456064 = ⟨1057976259, 1460497165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_145228032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_307233280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 307233280 = ⟨1681306522, 1384492704⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_153616640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_312476672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 312476672 = ⟨440188121, 714460670⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_156238336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_324010496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 324010496 = ⟨1234415776, 1552948336⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_162005248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_340787712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 340787712 = ⟨1416841433, 1255836801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_170393856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_346031104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 346031104 = ⟨667409179, 1770171037⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_173015552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_357564928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 357564928 = ⟨2047382449, 2116093560⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_178782464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_374342144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 374342144 = ⟨792439108, 230820411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_187171072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_379585536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 379585536 = ⟨1080830343, 1196541462⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_189792768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_391119360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 391119360 = ⟨325925096, 1306946911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_195559680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_407896576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 407896576 = ⟨1428472029, 1681985281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_203948288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_413139968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 413139968 = ⟨1189130906, 937749255⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_206569984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_424673792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 424673792 = ⟨1933178163, 379904412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_212336896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_441451008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 441451008 = ⟨317312015, 108395688⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_220725504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_446694400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 446694400 = ⟨1270997537, 1765408850⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_223347200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_458228224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 458228224 = ⟨1502515859, 1071226158⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_229114112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_475005440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 475005440 = ⟨1348751136, 1491001961⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_237502720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_480248832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 480248832 = ⟨1914474864, 440166738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_240124416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_491782656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 491782656 = ⟨581746394, 1560557129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_245891328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_508559872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 508559872 = ⟨773453707, 1095065769⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_254279936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_513803264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 513803264 = ⟨153621575, 797360221⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_256901632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_525337088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 525337088 = ⟨38822964, 768039306⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_262668544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_547357696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 547357696 = ⟨1749876144, 1252731563⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_273678848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_580912128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 580912128 = ⟨1164690642, 143822937⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_290456064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_614466560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 614466560 = ⟨1121751370, 1740718522⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_307233280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_648020992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 648020992 = ⟨2010056637, 1313310437⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_324010496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_681575424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 681575424 = ⟨1322319557, 473329924⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_340787712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_715129856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 715129856 = ⟨1899640059, 253271416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_357564928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_748684288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 748684288 = ⟨2103544920, 1810933791⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_374342144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_782238720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 782238720 = ⟨1783773358, 1443571294⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_391119360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_815793152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 815793152 = ⟨338572024, 377315934⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_407896576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_849347584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 849347584 = ⟨714460670, 1707295526⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_424673792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_882902016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 882902016 = ⟨1770171037, 1480074468⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_441451008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_916456448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 916456448 = ⟨1196541462, 1066653304⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_458228224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_950010880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 950010880 = ⟨937749255, 958352741⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_475005440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_983565312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 983565312 = ⟨1765408850, 876486110⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_491782656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1017119744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1017119744 = ⟨440166738, 233008783⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_508559872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1050674176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1050674176 = ⟨797360221, 1993862072⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_525337088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 320) = ⟨894752084, 1749876144⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 320 = 10486784 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_10486784

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨894752084, 1749876144⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 320) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 321) = ⟨1749876144, 1252731563⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 321 = 547357696 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_547357696

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1749876144, 1252731563⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 321) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 322) = ⟨1770167713, 338572024⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 322 = 278922240 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_278922240

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1770167713, 338572024⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 322) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 323) = ⟨338572024, 377315934⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 323 = 815793152 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_815793152

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨338572024, 377315934⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 323) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 324) = ⟨1674153723, 1322319557⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 324 = 144704512 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_144704512

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1674153723, 1322319557⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 324) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 325) = ⟨1322319557, 473329924⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 325 = 681575424 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_681575424

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1322319557, 473329924⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 325) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 326) = ⟨1189130906, 937749255⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 326 = 413139968 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_413139968

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1189130906, 937749255⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 326) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 327) = ⟨937749255, 958352741⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 327 = 950010880 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_950010880

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨937749255, 958352741⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 327) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 328) = ⟨406765125, 1121751370⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 328 = 77595648 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_77595648

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨406765125, 1121751370⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 328) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 329) = ⟨1121751370, 1740718522⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 329 = 614466560 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_614466560

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1121751370, 1740718522⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 329) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 330) = ⟨667409179, 1770171037⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 330 = 346031104 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_346031104

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨667409179, 1770171037⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 330) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 331) = ⟨1770171037, 1480074468⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 331 = 882902016 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_882902016

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1770171037, 1480074468⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 331) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 332) = ⟨336549856, 2103544920⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 332 = 211813376 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_211813376

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨336549856, 2103544920⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 332) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 333) = ⟨2103544920, 1810933791⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 333 = 748684288 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_748684288

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2103544920, 1810933791⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 333) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 334) = ⟨1914474864, 440166738⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 334 = 480248832 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_480248832

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1914474864, 440166738⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 334) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 335) = ⟨440166738, 233008783⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 335 = 1017119744 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1017119744

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨440166738, 233008783⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 335) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 336) = ⟨2003660710, 1164690642⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 336 = 44041216 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_44041216

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2003660710, 1164690642⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 336) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 337) = ⟨1164690642, 143822937⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 337 = 580912128 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_580912128

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1164690642, 143822937⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 337) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 338) = ⟨440188121, 714460670⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 338 = 312476672 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_312476672

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨440188121, 714460670⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 338) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 339) = ⟨714460670, 1707295526⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 339 = 849347584 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_849347584

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨714460670, 1707295526⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 339) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 340) = ⟨1894212231, 1899640059⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 340 = 178258944 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_178258944

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1894212231, 1899640059⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 340) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 341) = ⟨1899640059, 253271416⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 341 = 715129856 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_715129856

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1899640059, 253271416⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 341) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 342) = ⟨1270997537, 1765408850⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 342 = 446694400 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_446694400

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1270997537, 1765408850⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 342) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 343) = ⟨1765408850, 876486110⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 343 = 983565312 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_983565312

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1765408850, 876486110⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 343) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 344) = ⟨834173210, 2010056637⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 344 = 111150080 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_111150080

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨834173210, 2010056637⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 344) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 345) = ⟨2010056637, 1313310437⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 345 = 648020992 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_648020992

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2010056637, 1313310437⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 345) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 346) = ⟨1080830343, 1196541462⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 346 = 379585536 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_379585536

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1080830343, 1196541462⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 346) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 347) = ⟨1196541462, 1066653304⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 347 = 916456448 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_916456448

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1196541462, 1066653304⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 347) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 348) = ⟨703912353, 1783773358⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 348 = 245367808 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_245367808

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨703912353, 1783773358⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 348) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 349) = ⟨1783773358, 1443571294⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 349 = 782238720 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_782238720

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1783773358, 1443571294⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 349) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 350) = ⟨153621575, 797360221⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 350 = 513803264 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_513803264

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨153621575, 797360221⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 350) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 351) = ⟨797360221, 1993862072⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 351 = 1050674176 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1050674176

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨797360221, 1993862072⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 351) := by
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

end R17TableAChunk10Certificate
