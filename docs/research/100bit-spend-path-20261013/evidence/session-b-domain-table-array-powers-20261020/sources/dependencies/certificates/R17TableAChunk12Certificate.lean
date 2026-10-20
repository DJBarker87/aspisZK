import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk12Certificate
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

theorem power_67 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67 = ⟨1982486292, 1611456260⟩ := by
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

theorem power_73 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73 = ⟨1859610645, 698599623⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76 = ⟨2095288830, 1138360406⟩ := by
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

theorem power_83 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 83 = ⟨1069733101, 25059729⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_84 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84 = ⟨1543107831, 276086046⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42]
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

theorem power_92 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92 = ⟨1119524497, 1705494219⟩ := by
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

theorem power_105 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105 = ⟨244648141, 849348041⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108 = ⟨467798412, 1281237586⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54]
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

theorem power_116 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 116 = ⟨894357328, 342875169⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120 = ⟨1743886464, 1431800964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_121 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 121 = ⟨663578559, 2077989577⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124 = ⟨264684109, 401121384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_129 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 129 = ⟨635733977, 1147342686⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64]
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

theorem power_137 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 137 = ⟨1581084279, 1857932412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_140 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 140 = ⟨166789141, 776909418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_145 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 145 = ⟨1560614480, 360987849⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_147 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 147 = ⟨1871749785, 872210914⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 152 = ⟨186674930, 98941776⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_153 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 153 = ⟨1201477885, 724709579⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_161 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 161 = ⟨1737405672, 316991337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80]
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

theorem power_169 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 169 = ⟨2036465601, 1803091641⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_177 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 177 = ⟨1360111873, 1045548151⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_179 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 179 = ⟨64917534, 1646995590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_185 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 185 = ⟨1288520283, 160642759⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 192 = ⟨1343082982, 1656388718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_193 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 193 = ⟨631469289, 1565061397⟩ := by
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

theorem power_201 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 201 = ⟨1520147888, 325985670⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_204 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 204 = ⟨349974108, 1382066042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_209 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 209 = ⟨1797275270, 153051719⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_211 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 211 = ⟨2040897111, 1468235903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_217 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 217 = ⟨2139901027, 71265922⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_225 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 225 = ⟨601212348, 1809065373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_112]
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

theorem power_233 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 233 = ⟨145382460, 620920719⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_241 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 241 = ⟨1081438383, 1299194113⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_243 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 243 = ⟨1155190479, 56664675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_249 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 249 = ⟨1744129065, 1490136674⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_259 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 259 = ⟨1417755116, 754235764⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_129]
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

theorem power_275 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 275 = ⟨515463488, 783911294⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_137]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 280 = ⟨1151293179, 2142156513⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_140]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_291 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 291 = ⟨1366547540, 868920986⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_145]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_294 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 294 = ⟨1162279362, 654843129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_147]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 304 = ⟨1931014169, 1213553800⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_307 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 307 = ⟨1181458231, 154663034⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_153]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_323 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 323 = ⟨1964400221, 1702621100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_161]
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

theorem power_339 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 339 = ⟨165449130, 1824087556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_169]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_355 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 355 = ⟨490747431, 1598080402⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_177]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_358 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 358 = ⟨1922001538, 34318354⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_179]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_371 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 371 = ⟨1112480569, 1195892604⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_185]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 384 = ⟨1594705154, 1156423391⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_387 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 387 = ⟨604072873, 1300149367⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_193]
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

theorem power_403 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 403 = ⟨2097939792, 505543119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_201]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 408 = ⟨869725335, 1982977009⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_204]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_419 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 419 = ⟨848499905, 1850949985⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_209]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_422 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 422 = ⟨1600319089, 638267598⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_211]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_435 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 435 = ⟨877222603, 1715172086⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_217]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_451 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 451 = ⟨776527048, 209936995⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_225]
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

theorem power_467 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 467 = ⟨1341283340, 1470262178⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_233]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_483 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 483 = ⟨44923850, 959945043⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_241]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_486 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 486 = ⟨2035251788, 668739766⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_243]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_499 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 499 = ⟨1029352288, 331275798⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_249]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_518 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 518 = ⟨158998553, 537890622⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_259]
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

theorem power_550 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 550 = ⟨1241185395, 887661805⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_275]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 560 = ⟨1279482299, 2145341211⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_582 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 582 = ⟨433786515, 1835109513⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_291]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_588 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 588 = ⟨109266760, 756306898⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_294]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 608 = ⟨112946548, 968926260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_614 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 614 = ⟨1803214051, 1960118451⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_307]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_646 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 646 = ⟨264154216, 1665695067⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_323]
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

theorem power_678 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 678 = ⟨2125359533, 123864165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_339]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_710 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 710 = ⟨2001167712, 1637791072⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_355]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_716 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 716 = ⟨807928024, 181072667⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_358]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_742 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 742 = ⟨752463694, 260564666⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_371]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 768 = ⟨784830374, 912241638⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_774 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 774 = ⟨762512455, 1219280120⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_387]
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

theorem power_806 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 806 = ⟨864774403, 1967537191⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_403]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 816 = ⟨709216745, 661921156⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_838 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 838 = ⟨513840498, 743723607⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_419]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_844 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 844 = ⟨593422479, 1594591533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_422]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_870 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 870 = ⟨1789542798, 1122944099⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_435]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_902 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 902 = ⟨1061800146, 1394643040⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_451]
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

theorem power_934 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 934 = ⟨57616934, 1549197373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_467]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_966 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 966 = ⟨1708926149, 1101434556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_483]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_972 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 972 = ⟨10090051, 2036818165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_486]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_998 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 998 = ⟨524558114, 37607797⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_499]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1036 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1036 = ⟨1025230578, 246470654⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_518]
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

theorem power_1100 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1100 = ⟨346136448, 331587204⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_550]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1120 = ⟨428562734, 499127922⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1164 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1164 = ⟨1461641723, 704438001⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_582]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1176 = ⟨1337701156, 1198522828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_588]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1216 = ⟨222118537, 1014253609⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1228 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1228 = ⟨1181065478, 160532818⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_614]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1292 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1292 = ⟨550989153, 1759046137⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_646]
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

theorem power_1356 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1356 = ⟨945248571, 1442701781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_678]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1420 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1420 = ⟨622303395, 55953394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_710]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1432 = ⟨725452484, 1460220640⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_716]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1484 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1484 = ⟨335391997, 1719215948⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_742]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1536 = ⟨999230472, 1852479283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1548 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1548 = ⟨1006576664, 1613013421⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_774]
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

theorem power_1612 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1612 = ⟨1982745370, 399168465⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_806]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1632 = ⟨1906266428, 2062433102⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1676 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1676 = ⟨1243868302, 149511270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_838]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1688 = ⟨1792732, 1461195162⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_844]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1740 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1740 = ⟨612930459, 1067821025⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_870]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1804 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1804 = ⟨1093611765, 737591706⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_902]
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

theorem power_1868 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1868 = ⟨1878534224, 1396247579⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_934]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1932 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1932 = ⟨1977469052, 1981364443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_966]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1944 = ⟨301407602, 544320134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_972]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1996 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1996 = ⟨586729394, 1884844342⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_998]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2072 = ⟨94861523, 2114990683⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1036]
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

theorem power_2200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2200 = ⟨191306711, 1257080549⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1100]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2240 = ⟨1882985882, 1884234849⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2328 = ⟨657874299, 493146224⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1164]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2352 = ⟨993805021, 453742291⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2432 = ⟨1676081227, 1135991864⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2456 = ⟨1165494758, 1053160393⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1228]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2584 = ⟨1613611013, 564836753⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1292]
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

theorem power_2712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2712 = ⟨1543600783, 612742348⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1356]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2840 = ⟨1645691072, 1495180⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1420]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2864 = ⟨1307210844, 551960889⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2968 = ⟨1680633924, 1820323788⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1484]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3072 = ⟨2054061671, 949045631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3096 = ⟨839641135, 52299177⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1548]
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

theorem power_3224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3224 = ⟨1895519156, 609921201⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1612]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3264 = ⟨1045835668, 1112919339⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3352 = ⟨414672058, 1802855564⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1676]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3376 = ⟨357492176, 1415561852⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3480 = ⟨410093876, 483045812⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1740]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3608 = ⟨487166767, 641423420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1804]
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

theorem power_3736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3736 = ⟨1184284686, 1197056858⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1868]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3864 = ⟨256236981, 48406822⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1932]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3888 = ⟨2009665362, 160281151⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3992 = ⟨745048770, 688067711⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1996]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4144 = ⟨891346157, 1237677618⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2072]
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

theorem power_4400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4400 = ⟨1243231440, 1024224434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4480 = ⟨148358476, 1302044281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4656 = ⟨806593101, 529797795⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4704 = ⟨1156626838, 1971946255⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4864 = ⟨1327275430, 1972188598⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4912 = ⟨1399565252, 1634293471⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5168 = ⟨874275061, 378988305⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2584]
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

theorem power_5424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5424 = ⟨1943631909, 2076932052⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5680 = ⟨2081971902, 868862368⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5728 = ⟨1761772800, 2128352543⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5936 = ⟨1845633487, 230498648⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6145 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6145 = ⟨1533327559, 939725234⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6192 = ⟨1818299969, 306081010⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3096]
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

theorem power_6448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6448 = ⟨1142942987, 1411606839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6528 = ⟨491178846, 571176726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6704 = ⟨480724823, 113995248⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6752 = ⟨2033433106, 1697992958⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6960 = ⟨1547130223, 1349644126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7216 = ⟨889631762, 246409800⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3608]
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

theorem power_7472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7472 = ⟨1591027900, 922679478⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7728 = ⟨1993150498, 836747221⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7776 = ⟨2005898533, 1148783894⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7984 = ⟨276553622, 1718163583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8288 = ⟨1676338585, 2021666776⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4144]
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

theorem power_8800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8800 = ⟨1612117723, 53497435⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8960 = ⟨2091181541, 1615031214⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9312 = ⟨1623494602, 1653882898⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9408 = ⟨701979544, 793605973⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9728 = ⟨76857669, 1277280684⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9824 = ⟨787142344, 448621999⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10336 = ⟨1863286548, 1883219589⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5168]
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

theorem power_10848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10848 = ⟨468571499, 111518946⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11360 = ⟨1576968816, 1107523708⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11456 = ⟨1585333377, 1083459370⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11872 = ⟨477978380, 930226890⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12290 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12290 = ⟨942694747, 759293544⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6145]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12384 = ⟨60980301, 1978060137⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6192]
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

theorem power_12896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12896 = ⟨13804694, 1488746829⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13056 = ⟨1464918947, 1524839126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13408 = ⟨1805308613, 1735039902⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13504 = ⟨1113330667, 1443829141⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13920 = ⟨961089976, 1242518760⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14432 = ⟨1928445304, 1237150196⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7216]
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

theorem power_14944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14944 = ⟨1261142459, 1284494384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15456 = ⟨997672337, 723512202⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15552 = ⟨399467380, 1186469564⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15968 = ⟨1058289492, 541095093⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16576 = ⟨1530675029, 567422765⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8288]
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

theorem power_17600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17600 = ⟨1201679232, 128618018⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17920 = ⟨1517789543, 430872700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18624 = ⟨242655704, 1646681090⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18816 = ⟨1871025797, 143060818⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19456 = ⟨1672882969, 1149947594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19648 = ⟨369814260, 1994537627⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20672 = ⟨932411310, 1300860260⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10336]
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

theorem power_21696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21696 = ⟨1682085206, 741506572⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22720 = ⟨1152376624, 915016935⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22912 = ⟨103117915, 535771622⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23744 = ⟨917666273, 712489836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24580 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24580 = ⟨530643875, 741375440⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12290]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24768 = ⟨936523390, 2037084159⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12384]
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

theorem power_25792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25792 = ⟨1607714064, 2076237020⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26112 = ⟨733299889, 1597634788⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26816 = ⟨369278590, 224076404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27008 = ⟨1102569727, 1832459335⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27840 = ⟨1268409211, 2112557852⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28864 = ⟨516265109, 568166668⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14432]
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

theorem power_29888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29888 = ⟨694817491, 268760733⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30912 = ⟨1655422667, 1300169137⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31104 = ⟨827426978, 515986394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31936 = ⟨1347828335, 1317273520⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33152 = ⟨1561686338, 874130298⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16576]
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

theorem power_35200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35200 = ⟨519139677, 90305351⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35840 = ⟨1055573105, 1574974366⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37248 = ⟨1982304051, 8133230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37632 = ⟨1807268646, 1387828925⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38913 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38913 = ⟨658954270, 1503215334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39296 = ⟨1291678851, 326180711⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41344 = ⟨198262277, 1687947873⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20672]
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

theorem power_43392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43392 = ⟨737855930, 471042102⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45440 = ⟨371257233, 211408387⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45824 = ⟨922242157, 135837518⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47488 = ⟨1955860195, 740229084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49160 = ⟨164863045, 374127306⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24580]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49536 = ⟨1565707301, 323286829⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24768]
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

theorem power_51584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51584 = ⟨798928833, 1610217532⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52224 = ⟨1934269047, 1171518634⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53632 = ⟨1728081691, 1799487649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54016 = ⟨605949269, 1961649522⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55680 = ⟨714606537, 1260077229⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57728 = ⟨1843976884, 1595395262⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28864]
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

theorem power_59776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59776 = ⟨1997097917, 691951033⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61824 = ⟨1390915361, 736091053⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_62208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 62208 = ⟨753028638, 1902965361⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63872 = ⟨1152188036, 321012556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66304 = ⟨2101412446, 162241248⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33152]
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

theorem power_70400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70400 = ⟨1838178482, 339191808⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71681 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71681 = ⟨1574664703, 1675935543⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_74496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 74496 = ⟨1164574930, 1298303300⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_75264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 75264 = ⟨1546705477, 1945124534⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77826 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77826 = ⟨768601303, 1255370344⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38913]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_78592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 78592 = ⟨1820841606, 993316681⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_82688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 82688 = ⟨76509596, 1578443939⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41344]
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

theorem power_86784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86784 = ⟨1387531283, 956948167⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90880 = ⟨1753667047, 217671437⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_91648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 91648 = ⟨2067304729, 670477447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94976 = ⟨855983886, 699666906⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98320 = ⟨667325648, 694904467⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_99072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 99072 = ⟨554895131, 583815171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49536]
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

theorem power_103168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103168 = ⟨892959386, 834919794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104449 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104449 = ⟨1892274868, 1178705721⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_107264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 107264 = ⟨2050375505, 387363630⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_108032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 108032 = ⟨631069069, 1073533423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_111360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 111360 = ⟨36842238, 834753016⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115456 = ⟨250516810, 1239025439⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57728]
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

theorem power_119552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119552 = ⟨483075603, 1039982113⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123648 = ⟨1042103292, 1561906715⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_124416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 124416 = ⟨1226236584, 810920020⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_62208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_127744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 127744 = ⟨109435028, 461919757⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_132608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 132608 = ⟨1956997200, 1092499874⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_134144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 134144 = ⟨1388404629, 1554667997⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_137217 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 137217 = ⟨49595386, 1990380856⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_140800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 140800 = ⟨1025312410, 2114061797⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_143362 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 143362 = ⟨2122244918, 1863312535⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71681]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_148992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 148992 = ⟨253401567, 501717951⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_150528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 150528 = ⟨1556071938, 630300633⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_75264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_155652 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 155652 = ⟨174670259, 1416819985⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77826]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_157184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 157184 = ⟨1111240860, 1631310865⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_165376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 165376 = ⟨2109300178, 1625996594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_166912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 166912 = ⟨1012144713, 1307005340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_169985 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 169985 = ⟨1879395234, 2141644016⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_173568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 173568 = ⟨963832902, 1910953342⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_181760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 181760 = ⟨1272168483, 1986017399⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_183296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 183296 = ⟨328747162, 1067452003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_189952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 189952 = ⟨87421749, 559664752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_196640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 196640 = ⟨1765457798, 205692406⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_198144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 198144 = ⟨427859629, 1004977256⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_199680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 199680 = ⟨1914752554, 333151223⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_202753 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 202753 = ⟨280232926, 949991873⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_206336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 206336 = ⟨1524215797, 148765265⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_208898 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 208898 = ⟨1592556296, 1490276401⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104449]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_214528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 214528 = ⟨1560866466, 1678565034⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_107264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_216064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 216064 = ⟨111550904, 20507232⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_108032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_222720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 222720 = ⟨351531530, 286855972⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_230912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 230912 = ⟨214584703, 825570442⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_232448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 232448 = ⟨262887954, 1505590050⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_235521 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 235521 = ⟨705957609, 294967807⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_239104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 239104 = ⟨747344119, 1639196933⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_247296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 247296 = ⟨647295410, 1481557329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_248832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 248832 = ⟨1855084989, 994327263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_255488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 255488 = ⟨1655593893, 1865010071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_127744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_265216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 265216 = ⟨400258977, 1396357573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_132608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_268289 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 268289 = ⟨890363203, 1175492556⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_134144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_274434 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 274434 = ⟨626037919, 1389817791⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_137217]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_281600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 281600 = ⟨8030983, 585819917⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_140800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_286724 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 286724 = ⟨799422719, 239056211⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_143362]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_297984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 297984 = ⟨52503472, 2105957183⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_148992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_301057 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 301057 = ⟨487665247, 1434980911⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_150528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_311304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 311304 = ⟨1695963124, 1659122011⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_155652]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_314368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 314368 = ⟨1229069052, 17430875⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_157184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_330752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 330752 = ⟨382119912, 322693165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_165376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_333825 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 333825 = ⟨509152935, 1710248706⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_166912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_339970 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 339970 = ⟨1500196399, 707592266⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_169985]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_347136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 347136 = ⟨476301697, 173223609⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_173568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_363520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 363520 = ⟨1906577532, 225205074⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_181760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_366593 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 366593 = ⟨588983597, 122020123⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_183296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_379904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 379904 = ⟨1517022571, 1996711243⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_189952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_393280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 393280 = ⟨889679525, 823328191⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_196640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_396288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 396288 = ⟨1021149252, 373917733⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_198144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_399361 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 399361 = ⟨458349971, 315991398⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_199680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_405506 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 405506 = ⟨1692001611, 1502602194⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_202753]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_412672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 412672 = ⟨361555010, 1392782865⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_206336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_417796 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 417796 = ⟨1888187315, 1902340778⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_208898]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_429056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 429056 = ⟨6370254, 241078625⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_214528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_432129 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 432129 = ⟨568252126, 1482995016⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_216064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_445440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 445440 = ⟨1854007778, 974557353⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_222720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_461824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 461824 = ⟨441558666, 939698761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_230912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_464897 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 464897 = ⟨1895476927, 381082360⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_232448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_471042 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 471042 = ⟨775354876, 271837146⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_235521]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_478208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 478208 = ⟨1805825103, 1060877425⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_239104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_494592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 494592 = ⟨2068019499, 66137971⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_247296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_497665 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 497665 = ⟨1821140740, 1224869144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_248832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_510976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 510976 = ⟨710755422, 189309750⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_255488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_530433 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 530433 = ⟨922074292, 775651397⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_265216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_536578 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 536578 = ⟨1816599172, 771160352⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_268289]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_548868 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 548868 = ⟨1964115661, 702494439⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_274434]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_563201 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 563201 = ⟨2043670479, 142008122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_281600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_573448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 573448 = ⟨1447227247, 1853838961⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_286724]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_595969 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 595969 = ⟨1104671369, 1001873781⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_297984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_602114 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 602114 = ⟨2067539235, 412942653⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_301057]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_622608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 622608 = ⟨670699143, 39883701⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_311304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_628737 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 628737 = ⟨596028685, 366769522⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_314368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_661505 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 661505 = ⟨1501426283, 301018118⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_330752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_667650 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 667650 = ⟨944593802, 677053711⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_333825]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_679940 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 679940 = ⟨539796787, 359262527⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_339970]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_694273 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 694273 = ⟨1661102262, 1492663035⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_347136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_727041 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 727041 = ⟨783528168, 472532501⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_363520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_733186 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 733186 = ⟨1311733956, 23326518⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_366593]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_759809 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 759809 = ⟨712242956, 1439675385⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_379904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_786560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 786560 = ⟨1235270863, 866560323⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_393280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_792577 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 792577 = ⟨478802682, 1298332440⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_396288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_798722 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 798722 = ⟨2101592188, 931416197⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_399361]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_811012 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 811012 = ⟨1542871638, 1057681861⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_405506]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_825345 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 825345 = ⟨1821942972, 1132482971⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_412672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_835592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 835592 = ⟨927064864, 1054667086⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_417796]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_858113 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 858113 = ⟨310827237, 261062292⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_429056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_864258 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 864258 = ⟨1152165505, 1432779889⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_432129]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_890881 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 890881 = ⟨395456596, 820210032⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_445440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_923649 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 923649 = ⟨656851092, 118889378⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_461824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_929794 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 929794 = ⟨270114438, 1258083726⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_464897]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_942084 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 942084 = ⟨372741811, 316785386⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_471042]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_956417 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 956417 = ⟨1769186018, 1517649134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_478208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_989185 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 989185 = ⟨1623807647, 266630454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_494592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_995330 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 995330 = ⟨600014801, 909970248⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_497665]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1021953 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1021953 = ⟨1826276966, 2050899333⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_510976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1060866 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1060866 = ⟨108272410, 802648410⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_530433]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1073156 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1073156 = ⟨1730048156, 248462958⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_536578]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1097736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1097736 = ⟨69889604, 824483215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_548868]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1126402 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1126402 = ⟨648362272, 150178311⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_563201]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1146896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1146896 = ⟨1184697789, 688300251⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_573448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1191938 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1191938 = ⟨2005407724, 2021474445⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_595969]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1204228 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1204228 = ⟨216116439, 2135349384⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_602114]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1245216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1245216 = ⟨502704407, 922990771⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_622608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1257474 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1257474 = ⟨1826983421, 1520079488⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_628737]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1323010 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1323010 = ⟨222049158, 969463100⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_661505]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1335300 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1335300 = ⟨1426492025, 1983941075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_667650]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1359880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1359880 = ⟨2020758696, 122292688⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_679940]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1388546 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1388546 = ⟨1015297746, 1215242611⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_694273]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1454082 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1454082 = ⟨527690576, 1323785349⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_727041]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1466372 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1466372 = ⟨1633977779, 282050109⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_733186]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1519618 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1519618 = ⟨1116297086, 2003118056⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_759809]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1573120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1573120 = ⟨213229868, 1431041138⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_786560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1585154 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1585154 = ⟨1495078457, 1782441576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_792577]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1597444 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1597444 = ⟨1215391678, 2033509360⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_798722]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1622024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1622024 = ⟨1182101235, 478883630⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_811012]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1650690 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1650690 = ⟨180841515, 799013855⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_825345]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1671184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1671184 = ⟨1866009138, 1326399067⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_835592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1716226 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1716226 = ⟨2086367184, 1405311374⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_858113]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1728516 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1728516 = ⟨754437524, 371669943⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_864258]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1781762 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1781762 = ⟨177051592, 1384683287⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_890881]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1847298 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1847298 = ⟨1099955530, 1869657753⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_923649]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1859588 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1859588 = ⟨884487627, 551817868⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_929794]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1884168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1884168 = ⟨1123478068, 2000342197⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_942084]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1912834 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1912834 = ⟨1931337324, 2020474500⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_956417]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1978370 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1978370 = ⟨1482222275, 1667141607⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_989185]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1990660 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1990660 = ⟨1349139005, 517794828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_995330]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2043906 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2043906 = ⟨1478044346, 2133960898⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1021953]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2121732 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2121732 = ⟨360944894, 537853864⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1060866]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2146312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2146312 = ⟨1649919760, 551086525⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1073156]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2195472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2195472 = ⟨2078436872, 1090090627⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1097736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2252804 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2252804 = ⟨2002019935, 919033233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1126402]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2293792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2293792 = ⟨990284422, 2114039390⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1146896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2383876 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2383876 = ⟨154647932, 895579442⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1191938]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2408456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2408456 = ⟨1607923126, 1956940244⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1204228]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2490432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2490432 = ⟨1238237187, 1817001346⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1245216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2514948 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2514948 = ⟨1410289317, 235954768⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1257474]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2646020 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2646020 = ⟨488243670, 457722093⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1323010]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2670600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2670600 = ⟨907721438, 244814443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1335300]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2719760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2719760 = ⟨1709893172, 1922382059⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1359880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2777092 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2777092 = ⟨1104380019, 1669674824⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1388546]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2908164 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2908164 = ⟨1405947881, 280689607⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1454082]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2932744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2932744 = ⟨1401702779, 1366077274⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1466372]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3039236 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3039236 = ⟨984756022, 455311690⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1519618]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3146240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3146240 = ⟨1575411460, 1169668770⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1573120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3170308 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3170308 = ⟨1438950504, 178837418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1585154]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3194888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3194888 = ⟨294442086, 1023393418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1597444]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3244048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3244048 = ⟨1241067391, 876590300⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1622024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3301380 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3301380 = ⟨1793940899, 83503670⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1650690]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3342368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3342368 = ⟨245494204, 1253989854⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1671184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3432452 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3432452 = ⟨1326376425, 1657853022⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1716226]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3457032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3457032 = ⟨284505412, 632480057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1728516]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3563524 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3563524 = ⟨1515753775, 1620780596⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1781762]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3694596 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3694596 = ⟨1371042105, 1496001738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1847298]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3719176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3719176 = ⟨1504233360, 1035689076⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1859588]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3768336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3768336 = ⟨1249325254, 716877558⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1884168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3825668 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3825668 = ⟨712925285, 2093058326⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1912834]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3956740 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3956740 = ⟨346497587, 152934991⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1978370]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3981320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3981320 = ⟨881960699, 1895124675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1990660]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4087812 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4087812 = ⟨2016435628, 612576836⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2043906]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4243464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4243464 = ⟨76595285, 907306648⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2121732]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4292624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4292624 = ⟨1718684676, 460341394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2146312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4390944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4390944 = ⟨983775369, 276909204⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2195472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4505608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4505608 = ⟨822999681, 1533799927⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2252804]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4587584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4587584 = ⟨1357483097, 777932811⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2293792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4767752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4767752 = ⟨1617200629, 77696695⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2383876]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4816912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4816912 = ⟨666940987, 1054852102⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2408456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4980864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4980864 = ⟨1254393640, 669787096⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2490432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5029896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5029896 = ⟨493231820, 887118152⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2514948]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5292040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5292040 = ⟨1144150530, 1006083437⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2646020]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5341200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5341200 = ⟨2025576327, 2109172044⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2670600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5439520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5439520 = ⟨2121251290, 1626959625⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2719760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5554184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5554184 = ⟨197050159, 939776453⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2777092]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5816328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5816328 = ⟨302560880, 981318619⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2908164]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5865488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5865488 = ⟨1481626698, 1261257505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2932744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6078472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6078472 = ⟨91137136, 1748988711⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3039236]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6292480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6292480 = ⟨1421224217, 977701755⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3146240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6340616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6340616 = ⟨1687913828, 739903748⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3170308]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6389776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6389776 = ⟨476198913, 2064289397⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3194888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6488096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6488096 = ⟨222036113, 1140478773⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3244048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6602760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6602760 = ⟨784425496, 25806938⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3301380]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6684736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6684736 = ⟨147814313, 514367437⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3342368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6864904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6864904 = ⟨1704339248, 879461866⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3432452]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6914064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6914064 = ⟨49855037, 1499490492⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3457032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7127048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7127048 = ⟨1557536806, 375311693⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3563524]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7389192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7389192 = ⟨1952427909, 2063590532⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3694596]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7438352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7438352 = ⟨1321044514, 322941794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3719176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7536672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7536672 = ⟨157430027, 751719042⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3768336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7651336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7651336 = ⟨1940301761, 335808064⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3825668]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7913480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7913480 = ⟨1021400615, 751535568⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3956740]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7962640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7962640 = ⟨1169092355, 1893447902⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3981320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8175624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8175624 = ⟨1732401906, 1039475187⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4087812]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8486928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8486928 = ⟨814913503, 843823045⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4243464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8585248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8585248 = ⟨1009376795, 1717506769⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4292624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8781888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8781888 = ⟨1939728733, 1601960881⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4390944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9011216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9011216 = ⟨906876068, 1857345761⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4505608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9175168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9175168 = ⟨875700483, 868534462⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4587584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9535504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9535504 = ⟨1815029940, 24571001⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4767752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9633824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9633824 = ⟨1092683152, 703238282⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4816912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9961728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9961728 = ⟨277823625, 2029823086⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4980864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10059792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10059792 = ⟨436868090, 1747268148⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5029896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10584080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10584080 = ⟨2038822632, 822697665⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5292040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10682400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10682400 = ⟨756982255, 746559197⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5341200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10879040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10879040 = ⟨230312478, 279869991⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5439520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11108368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11108368 = ⟨1195253626, 152144007⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5554184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11632656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11632656 = ⟨1461438925, 256579305⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5816328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11730976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11730976 = ⟨625554982, 1936947357⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5865488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12156944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12156944 = ⟨875916023, 124512262⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6078472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12681232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12681232 = ⟨2002360547, 1373703215⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6340616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12779552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12779552 = ⟨1453287357, 1955446546⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6389776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12976192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12976192 = ⟨2125282492, 1920521784⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6488096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13205520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13205520 = ⟨2109016533, 940451516⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6602760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13369472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13369472 = ⟨397384086, 15862107⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6684736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13729808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13729808 = ⟨1170120183, 1351364400⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6864904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13828128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13828128 = ⟨595375962, 277444233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6914064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14254096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14254096 = ⟨768439324, 212292150⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7127048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14778384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14778384 = ⟨1572184451, 1106222211⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7389192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14876704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14876704 = ⟨1381600015, 2025058896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7438352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15073344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15073344 = ⟨956473698, 728407306⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7536672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15302672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15302672 = ⟨359619544, 761546402⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7651336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15826960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15826960 = ⟨1694633676, 1176963746⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7913480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15925280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15925280 = ⟨374621591, 1560164188⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7962640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16351248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16351248 = ⟨684192527, 1855310565⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8175624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16973856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16973856 = ⟨231136278, 362056991⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8486928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17170496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17170496 = ⟨1396722055, 1541311975⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8585248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17563776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17563776 = ⟨242605017, 2044031276⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8781888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18022432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18022432 = ⟨540503025, 793054165⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9011216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18350336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18350336 = ⟨1835870457, 919478271⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9175168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19071008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19071008 = ⟨1744881983, 671751544⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9535504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19267648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19267648 = ⟨1623524949, 1405344419⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9633824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19923456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19923456 = ⟨384725898, 1657861462⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9961728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20119584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20119584 = ⟨1019630104, 344541255⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10059792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21168160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21168160 = ⟨2099579527, 649921948⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10584080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21364800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21364800 = ⟨1622416546, 1059630367⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10682400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21758080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21758080 = ⟨755794786, 1103309912⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10879040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22216736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22216736 = ⟨758881899, 1900221331⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11108368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23265312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23265312 = ⟨53654792, 808667701⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11632656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23461952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23461952 = ⟨1744377250, 1811340730⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11730976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24313888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24313888 = ⟨1216737032, 921211356⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12156944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25362464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25362464 = ⟨1155162253, 921861776⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12681232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25559104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25559104 = ⟨2061317861, 925459048⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12779552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25952384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25952384 = ⟨1673349169, 1344840516⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12976192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26411040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26411040 = ⟨1242465526, 305652002⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13205520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26738944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26738944 = ⟨523591672, 261443607⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13369472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27459616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27459616 = ⟨1346045177, 594212987⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13729808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27656256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27656256 = ⟨280031962, 2080546012⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13828128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28508192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28508192 = ⟨600458483, 379924614⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14254096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29556768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29556768 = ⟨2004742893, 1038107533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14778384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29753408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29753408 = ⟨434407264, 1697166423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14876704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30146688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30146688 = ⟨1364296345, 1710984276⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15073344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30605344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30605344 = ⟨1941201543, 1193164699⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15302672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31653920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31653920 = ⟨125854693, 10651753⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15826960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31850560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31850560 = ⟨1808784623, 42908758⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15925280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32702496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32702496 = ⟨170612291, 456761699⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16351248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33947712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33947712 = ⟨1500698388, 2125382600⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16973856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34340992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34340992 = ⟨830966187, 111693764⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17170496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35127552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35127552 = ⟨1569875226, 423244304⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17563776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36044864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36044864 = ⟨777670064, 624282116⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18022432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36700672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36700672 = ⟨608834082, 1238660785⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18350336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38142016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38142016 = ⟨1164609809, 1481760474⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19071008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38535296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38535296 = ⟨272998908, 198474586⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19267648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39846912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39846912 = ⟨162657442, 1560528002⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19923456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40239168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40239168 = ⟨1755120888, 1969184801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20119584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42336320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42336320 = ⟨933129458, 1654895907⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21168160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42729600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42729600 = ⟨539360719, 1751164307⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21364800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_43516160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43516160 = ⟨821067323, 1599740454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21758080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44433472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44433472 = ⟨715952065, 2114616534⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22216736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46530624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46530624 = ⟨1316063652, 1195388211⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23265312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46923904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46923904 = ⟨249134102, 1409982773⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23461952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48627776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48627776 = ⟨1294881434, 1001550394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24313888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50724928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50724928 = ⟨1127158175, 778604029⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25362464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51118208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51118208 = ⟨439168923, 386104287⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25559104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51904768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51904768 = ⟨1088092648, 850964227⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25952384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52822080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52822080 = ⟨1704906635, 6060986⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26411040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53477888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53477888 = ⟨1888215546, 1172017247⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26738944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54919232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54919232 = ⟨978401085, 1391695677⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27459616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55312512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55312512 = ⟨681321967, 1943706534⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27656256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57016384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57016384 = ⟨1008711678, 58930868⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28508192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59113536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59113536 = ⟨1325872656, 304900494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29556768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59506816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59506816 = ⟨1604747719, 782246062⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29753408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_60293376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 60293376 = ⟨1513503044, 1475300475⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30146688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61210688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61210688 = ⟨1286964450, 1596231252⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30605344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63307840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63307840 = ⟨618065179, 2136755923⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31653920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63701120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63701120 = ⟨1543044125, 362441201⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31850560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65404992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65404992 = ⟨683922270, 1882091123⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32702496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_67895424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67895424 = ⟨1376348000, 2002182282⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33947712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_68681984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 68681984 = ⟨186227273, 941182532⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34340992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_70255104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70255104 = ⟨1140445689, 1786056859⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35127552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_72089728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 72089728 = ⟨272171287, 457136002⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36044864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73401344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73401344 = ⟨779436839, 223436892⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36700672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76284032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76284032 = ⟨909692709, 1270363639⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38142016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_77070592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 77070592 = ⟨1959853279, 1325402892⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38535296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_80478336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 80478336 = ⟨1536242146, 1545616187⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40239168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_84672640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84672640 = ⟨2055208177, 356833767⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42336320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_85459200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 85459200 = ⟨1125625629, 612145747⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42729600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_87032320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 87032320 = ⟨1059620925, 896489236⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43516160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88866944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88866944 = ⟨1016507636, 249694180⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44433472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_93061248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93061248 = ⟨1505192714, 1291132154⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46530624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_93847808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93847808 = ⟨106212639, 1767438171⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46923904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_97255552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 97255552 = ⟨957456785, 1555332228⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48627776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_101449856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101449856 = ⟨767013124, 1247383674⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50724928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102236416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102236416 = ⟨224749126, 126061550⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51118208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_103809536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 103809536 = ⟨1742939529, 2008237461⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51904768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105644160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105644160 = ⟨755430420, 1924137146⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52822080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_106955776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 106955776 = ⟨534092016, 1184883641⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53477888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_109838464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109838464 = ⟨2116953151, 1463963141⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54919232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_110625024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110625024 = ⟨2073204388, 1593829058⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55312512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_114032768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 114032768 = ⟨2147338427, 863675936⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57016384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_118227072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118227072 = ⟨573263943, 38402113⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59113536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_119013632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119013632 = ⟨313545691, 691611879⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59506816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_120586752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 120586752 = ⟨170353440, 50752381⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_60293376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122421376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122421376 = ⟨353160565, 1143156290⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61210688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126615680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126615680 = ⟨1320328756, 830402392⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63307840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_127402240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 127402240 = ⟨555617322, 495588017⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63701120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_130809984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 130809984 = ⟨963071083, 1724969842⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65404992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_135790848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 135790848 = ⟨1176822343, 881085484⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67895424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_137363968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 137363968 = ⟨208185576, 463158619⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68681984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_140510208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 140510208 = ⟨963110699, 493845922⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70255104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_144179456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 144179456 = ⟨1016796018, 584898589⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72089728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_152568064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 152568064 = ⟨1971963564, 1522249521⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76284032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_154141184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 154141184 = ⟨1300747162, 461695798⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_77070592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_160956672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 160956672 = ⟨1920648776, 238681913⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80478336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_169345280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 169345280 = ⟨881568269, 545838334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84672640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_170918400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 170918400 = ⟨5435898, 1919050489⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85459200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_174064640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 174064640 = ⟨24486645, 110112918⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_87032320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_177733888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 177733888 = ⟨1055750181, 1187011584⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88866944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_186122496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 186122496 = ⟨1340008484, 380414313⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93061248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_187695616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 187695616 = ⟨192291839, 1677762294⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93847808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_194511104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 194511104 = ⟨223794407, 759520871⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_97255552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_202899712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 202899712 = ⟨216363079, 1411225379⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101449856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_204472832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 204472832 = ⟨1929218170, 114347567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102236416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_207619072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 207619072 = ⟨1368395169, 2122900869⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_103809536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_211288320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 211288320 = ⟨1660554012, 709550966⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105644160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_219676928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 219676928 = ⟨407985919, 979976484⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109838464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_221250048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 221250048 = ⟨1979839719, 1929406319⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110625024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_228065536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 228065536 = ⟨1375507506, 1525954230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_114032768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_236454144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 236454144 = ⟨1816857084, 725560450⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118227072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_238027264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 238027264 = ⟨1856278441, 1576758254⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119013632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_241173504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 241173504 = ⟨903868214, 1028549284⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_120586752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_244842752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 244842752 = ⟨983930965, 1624713431⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122421376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_253231360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 253231360 = ⟨82692416, 2118038230⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126615680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_254804480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 254804480 = ⟨1845164141, 903072269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_127402240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_261619968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 261619968 = ⟨693112906, 153828650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_130809984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_271581696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 271581696 = ⟨1288938398, 1842276304⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_135790848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_274727936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 274727936 = ⟨1514835708, 825288080⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_137363968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_288358912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 288358912 = ⟨879786431, 1088834530⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_144179456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_305136128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 305136128 = ⟨1147792926, 843556234⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_152568064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_308282368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 308282368 = ⟨1553098421, 1743803217⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_154141184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_321913344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 321913344 = ⟨959264359, 1462916431⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_160956672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_338690560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 338690560 = ⟨1900719726, 525411963⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_169345280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_341836800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 341836800 = ⟨1371651014, 244997852⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_170918400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_355467776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 355467776 = ⟨1873343639, 1735095878⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_177733888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_372244992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 372244992 = ⟨898621334, 268832720⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_186122496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_375391232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 375391232 = ⟨1045751413, 627353290⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_187695616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_389022208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 389022208 = ⟨1733201197, 70154463⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_194511104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_405799424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 405799424 = ⟨1931585539, 1245286194⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_202899712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_408945664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 408945664 = ⟨845600471, 1262183431⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_204472832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_422576640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 422576640 = ⟨1600678156, 198036989⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_211288320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_439353856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 439353856 = ⟨712635061, 947909135⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_219676928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_442500096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 442500096 = ⟨1774553093, 1188070682⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_221250048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_456131072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 456131072 = ⟨1635446646, 1031526538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_228065536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_472908288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 472908288 = ⟨726989262, 584717267⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_236454144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_476054528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 476054528 = ⟨2039730200, 1811033336⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_238027264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_489685504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 489685504 = ⟨774629634, 960756990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_244842752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_506462720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 506462720 = ⟨2110540959, 1847750486⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_253231360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_509608960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 509608960 = ⟨753759022, 1035405166⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_254804480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_523239936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 523239936 = ⟨1631429582, 1758447576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_261619968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_543163392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 543163392 = ⟨977701755, 726259430⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_271581696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_576717824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 576717824 = ⟨1560528002, 1984826205⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_288358912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_610272256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 610272256 = ⟨223436892, 1368046808⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_305136128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_643826688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 643826688 = ⟨1184883641, 1613391631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_321913344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_677381120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 677381120 = ⟨493845922, 1184372948⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_338690560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_710935552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 710935552 = ⟨110112918, 2122997002⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_355467776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_744489984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 744489984 = ⟨2122900869, 779088478⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_372244992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_778044416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 778044416 = ⟨1028549284, 1243615433⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_389022208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_811598848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 811598848 = ⟨825288080, 632647939⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_405799424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_845153280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 845153280 = ⟨1743803217, 594385226⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_422576640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_878707712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 878707712 = ⟨244997852, 775832633⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_439353856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_912262144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 912262144 = ⟨627353290, 1101732234⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_456131072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_945816576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 945816576 = ⟨1262183431, 1301883176⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_472908288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_979371008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 979371008 = ⟨1188070682, 372930554⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_489685504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1012925440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1012925440 = ⟨1811033336, 107753447⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_506462720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1046479872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1046479872 = ⟨1035405166, 1393724625⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_523239936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 384) = ⟨1421224217, 977701755⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 384 = 6292480 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_6292480

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1421224217, 977701755⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 384) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 385) = ⟨977701755, 726259430⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 385 = 543163392 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_543163392

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨977701755, 726259430⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 385) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 386) = ⟨1514835708, 825288080⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 386 = 274727936 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_274727936

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1514835708, 825288080⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 386) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 387) = ⟨825288080, 632647939⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 387 = 811598848 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_811598848

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨825288080, 632647939⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 387) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 388) = ⟨963110699, 493845922⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 388 = 140510208 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_140510208

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨963110699, 493845922⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 388) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 389) = ⟨493845922, 1184372948⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 389 = 677381120 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_677381120

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨493845922, 1184372948⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 389) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 390) = ⟨845600471, 1262183431⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 390 = 408945664 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_408945664

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨845600471, 1262183431⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 390) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 391) = ⟨1262183431, 1301883176⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 391 = 945816576 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_945816576

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1262183431, 1301883176⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 391) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 392) = ⟨779436839, 223436892⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 392 = 73401344 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_73401344

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨779436839, 223436892⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 392) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 393) = ⟨223436892, 1368046808⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 393 = 610272256 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_610272256

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨223436892, 1368046808⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 393) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 394) = ⟨1371651014, 244997852⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 394 = 341836800 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_341836800

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1371651014, 244997852⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 394) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 395) = ⟨244997852, 775832633⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 395 = 878707712 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_878707712

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨244997852, 775832633⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 395) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 396) = ⟨1368395169, 2122900869⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 396 = 207619072 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_207619072

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1368395169, 2122900869⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 396) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 397) = ⟨2122900869, 779088478⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 397 = 744489984 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_744489984

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2122900869, 779088478⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 397) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 398) = ⟨2039730200, 1811033336⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 398 = 476054528 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_476054528

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2039730200, 1811033336⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 398) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 399) = ⟨1811033336, 107753447⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 399 = 1012925440 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1012925440

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1811033336, 107753447⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 399) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 400) = ⟨162657442, 1560528002⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 400 = 39846912 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_39846912

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨162657442, 1560528002⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 400) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 401) = ⟨1560528002, 1984826205⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 401 = 576717824 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_576717824

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1560528002, 1984826205⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 401) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 402) = ⟨1553098421, 1743803217⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 402 = 308282368 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_308282368

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1553098421, 1743803217⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 402) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 403) = ⟨1743803217, 594385226⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 403 = 845153280 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_845153280

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1743803217, 594385226⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 403) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 404) = ⟨24486645, 110112918⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 404 = 174064640 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_174064640

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨24486645, 110112918⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 404) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 405) = ⟨110112918, 2122997002⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 405 = 710935552 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_710935552

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨110112918, 2122997002⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 405) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 406) = ⟨1774553093, 1188070682⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 406 = 442500096 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_442500096

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1774553093, 1188070682⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 406) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 407) = ⟨1188070682, 372930554⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 407 = 979371008 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_979371008

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1188070682, 372930554⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 407) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 408) = ⟨534092016, 1184883641⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 408 = 106955776 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_106955776

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨534092016, 1184883641⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 408) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 409) = ⟨1184883641, 1613391631⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 409 = 643826688 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_643826688

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1184883641, 1613391631⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 409) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 410) = ⟨1045751413, 627353290⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 410 = 375391232 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_375391232

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1045751413, 627353290⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 410) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 411) = ⟨627353290, 1101732234⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 411 = 912262144 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_912262144

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨627353290, 1101732234⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 411) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 412) = ⟨903868214, 1028549284⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 412 = 241173504 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_241173504

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨903868214, 1028549284⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 412) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 413) = ⟨1028549284, 1243615433⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 413 = 778044416 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_778044416

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1028549284, 1243615433⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 413) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 414) = ⟨753759022, 1035405166⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 414 = 509608960 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_509608960

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨753759022, 1035405166⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 414) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 415) = ⟨1035405166, 1393724625⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 415 = 1046479872 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1046479872

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1035405166, 1393724625⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 415) := by
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

end R17TableAChunk12Certificate
